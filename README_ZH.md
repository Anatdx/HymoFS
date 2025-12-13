# HymoFS 技术文档

## 概述
HymoFS 是一个内核级的路径操控和隐藏框架，专为 Android 上的高级覆盖和修改功能而设计。与传统的 OverlayFS 不同，它通过直接 Hook Linux 内核的 VFS（虚拟文件系统）层来工作，从而对用户空间应用程序透明地拦截和修改文件操作。

## 控制接口
与内核模块的通信通过字符设备节点进行处理：
`/dev/hymo_ctl`

通信协议使用标准的 `ioctl` 系统调用，定义在 `fs/hymofs_ioctl.h` 中。

### 命令 (IOCTL)

所有命令都通过 `ioctl(fd, CMD, &arg)` 发送，其中 `fd` 是打开 `/dev/hymo_ctl` 的文件描述符。

#### 1. Clear (清除)
重置所有规则并使内部缓存失效。
*   **IOCTL**: `HYMO_IOC_CLEAR_ALL`
*   **参数**: 无
*   **效果**: 清空所有哈希表（重定向、隐藏、注入）并增加内部版本计数器 (`hymo_version`)。

#### 2. Add (重定向)
将源路径的访问重定向到目标路径。
*   **IOCTL**: `HYMO_IOC_ADD_RULE`
*   **参数**: `struct hymo_ioctl_arg`
    *   `src`: 源路径字符串指针
    *   `target`: 目标路径字符串指针
    *   `type`: 文件类型 (DT_DIR=4, DT_REG=8 等)
*   **机制**: Hook 了 `fs/namei.c` 中的 `getname_flags`。当进程请求 `/source/path` 时，内核会透明地将其替换为 `/target/path`。

#### 3. Hide (隐藏)
从系统中彻底隐藏一个路径。
*   **IOCTL**: `HYMO_IOC_HIDE_RULE`
*   **参数**: `struct hymo_ioctl_arg`
    *   `src`: 要隐藏的路径
*   **效果**:
    *   **访问**: 通过 `open`、`access` 等方式访问时，返回 `-ENOENT` (No such file or directory)。
    *   **列表**: 在 `readdir` 操作期间过滤掉该条目，使其对 `ls` 不可见。

#### 4. Inject (目录注入)
在目录列表中启用“幽灵”文件。
*   **IOCTL**: `HYMO_IOC_INJECT_RULE`
*   **参数**: `struct hymo_ioctl_arg`
    *   `src`: 目标目录路径
*   **机制**:
    *   **列表**: Hook 了 `getdents/getdents64`。在真实的目录条目列出之后，HymoFS 会人为地追加那些位于该目录下且由 `add` 规则定义的条目。
    *   **Mtime 伪装**: Hook 了 `fs/stat.c` 中的 `vfs_getattr`。强制将目录的修改时间 (`mtime`) 和改变时间 (`ctime`) 报告为当前系统时间。

#### 5. Delete (删除)
根据键路径删除特定的规则。
*   **IOCTL**: `HYMO_IOC_DEL_RULE`
*   **参数**: `struct hymo_ioctl_arg`
    *   `src`: 规则的键路径
*   **效果**: 在所有哈希表中搜索给定的键并删除。

#### 6. List (列出规则)
获取当前所有活动规则的列表。
*   **操作**: `read()` 系统调用
*   **机制**: 直接读取 `/dev/hymo_ctl` 设备文件。内核会生成包含所有规则的文本格式数据。
*   **格式**:
    ```text
    HymoFS Protocol: 4
    HymoFS Config Version: 123
    add /source /target 8
    hide /path/to/hide
    inject /path/to/inject
    ```

## 实现细节

### 1. 架构设计
*   **hymofs_ioctl.h**: 定义了用户空间 API (UAPI)，包括 `ioctl` 命令码和数据结构。用户态工具只需包含此头文件。
*   **hymofs.h**: 内核模块内部实现头文件，包含内核数据结构和函数声明。
*   **hymofs.c**: 核心逻辑实现，包括字符设备注册、ioctl 处理、哈希表管理等。

### 2. 路径解析 Hook (`fs/namei.c`)
*   **函数**: `getname_flags`
*   **逻辑**:
    1.  **隐藏检查**: 检查解析出的文件名是否在 `hymo_hide_paths` 哈希表中。如果存在，立即返回 `ERR_PTR(-ENOENT)`。
    2.  **重定向检查**: 检查文件名是否在 `hymo_paths` 哈希表中。如果存在，解析目标路径并使用新路径重新开始查找 (`getname_kernel`)。

### 3. 目录列表 Hook (`fs/readdir.c`)
*   **函数**: `filldir`, `filldir64`, `getdents`, `getdents64`
*   **隐藏**: 在 `filldir` 回调内部，检查当前条目名称（结合目录路径）是否匹配隐藏路径。如果匹配，则返回 `true` 而不将数据复制到用户缓冲区。
*   **注入**:
    *   使用一个“魔法位置”常量：`HYMO_MAGIC_POS` (`0x7000000000000000ULL`)。
    *   当标准目录列表完成时，HymoFS 接管操作，调用 `hymofs_populate_injected_list` 扫描并注入“幽灵”条目。

### 4. 属性 Hook (`fs/stat.c`)
*   **函数**: `vfs_getattr_nosec`
*   **逻辑**: 如果目录在 **注入列表** 中，内核会用 `ktime_get_real_ts64()` 覆盖返回的 `mtime` 和 `ctime`，确保应用程序感知到目录内容的变化。

## 数据结构
*   **哈希表**: 使用 10 位（1024 个桶）的 `DEFINE_HASHTABLE` 进行快速查找。
*   **并发**: 由全局自旋锁 `hymo_lock` 保护。
*   **内存管理**: 使用 `vmalloc` 分配大块内存（如 `read` 操作的缓冲区），确保稳定性。
