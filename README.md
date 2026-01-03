# HymoFS

> **Warning**: This is an experimental kernel modification.

HymoFS is a kernel patch designed to inject virtual entries into directory listings by modifying the `getdents` system call.

## Risks & Limitations

*   **System Instability**: Modifying core filesystem syscalls is highly intrusive and may lead to kernel panics or system freezes.
*   **Performance Impact**: The injection logic adds overhead to every directory read operation, potentially degrading I/O performance.
*   **Compatibility Issues**: This patch may conflict with other filesystem modifications or security modules.
*   **Data Integrity**: While intended to be read-only injection, bugs in the implementation could theoretically affect filesystem stability.

## Usage

This patch is intended for developers and advanced users who understand the risks involved in kernel-level modifications.
