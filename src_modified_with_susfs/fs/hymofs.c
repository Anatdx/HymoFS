#include <linux/string.h>
#include <linux/mm.h>
#include <linux/file.h>
#include <linux/fdtable.h>
#include <linux/fsnotify.h>
#include <linux/module.h>
#include <linux/tty.h>
#include <linux/namei.h>
#include <linux/backing-dev.h>
#include <linux/capability.h>
#include <linux/securebits.h>
#include <linux/security.h>
#include <linux/mount.h>
#include <linux/fcntl.h>
#include <linux/slab.h>
#include <linux/uaccess.h>
#include <linux/fs.h>
#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include <linux/dcache.h>
#include <linux/path.h>
#include <linux/hashtable.h>
#include <linux/init.h>
#include <linux/time.h>
#include <linux/dirent.h>
#include <linux/miscdevice.h>
#include <linux/cred.h>
#include <linux/uidgid.h>
#include <linux/vmalloc.h>
#include <linux/atomic.h>
#include <linux/spinlock.h>
#include <linux/kernel.h>
#include <linux/mnt_namespace.h>
#include <linux/nsproxy.h>
#include <linux/sched.h>
#include <linux/fs_struct.h>
#include <linux/sched/task.h>
#include "mount.h"

#include "hymofs.h"
#include <linux/hymo_magic.h>

extern int (*hymo_dispatch_cmd_hook)(unsigned int cmd, void __user *arg);

#ifdef CONFIG_HYMOFS_USE_KSU
extern bool susfs_is_current_ksu_domain(void);
#endif

extern bool hymo_is_avc_log_spoofing_enabled;

#ifdef CONFIG_HYMOFS

#define HYMO_HASH_BITS 16

struct hymo_entry {
    char *src;
    char *target;
    unsigned char type;
    struct hlist_node node;
    struct hlist_node target_node;
};
struct hymo_hide_entry {
    char *path;
    struct hlist_node node;
};

struct hymo_inject_entry {
    char *dir;
    struct hlist_node node;
};

struct hymo_xattr_sb_entry {
    struct super_block *sb;
    struct hlist_node node;
};

struct hymo_merge_entry {
    char *src;
    char *target;
    struct hlist_node node;
};

static DEFINE_HASHTABLE(hymo_paths, HYMO_HASH_BITS);
static DEFINE_HASHTABLE(hymo_targets, HYMO_HASH_BITS);
static DEFINE_HASHTABLE(hymo_hide_paths, HYMO_HASH_BITS);
static DEFINE_HASHTABLE(hymo_inject_dirs, HYMO_HASH_BITS);
static DEFINE_HASHTABLE(hymo_xattr_sbs, HYMO_HASH_BITS);
static DEFINE_HASHTABLE(hymo_merge_dirs, HYMO_HASH_BITS);
static DEFINE_SPINLOCK(hymo_lock);
atomic_t hymo_atomiconfig = ATOMIC_INIT(0);
EXPORT_SYMBOL(hymo_atomiconfig);

static bool hymo_debug_enabled = false;
module_param(hymo_debug_enabled, bool, 0644);
MODULE_PARM_DESC(hymo_debug_enabled, "Enable debug logging");
static bool hymo_stealth_enabled = true;

static char hymo_mirror_path_buf[PATH_MAX] = HYMO_DEFAULT_MIRROR_PATH;
static char hymo_mirror_name_buf[NAME_MAX] = HYMO_DEFAULT_MIRROR_NAME;
static char *hymo_current_mirror_path = hymo_mirror_path_buf;
static char *hymo_current_mirror_name = hymo_mirror_name_buf;

#define hymo_log(fmt, ...) do { \
    if (hymo_debug_enabled) \
        printk(KERN_INFO "hymofs: " fmt, ##__VA_ARGS__); \
} while(0)

static void hymo_cleanup(void) {
    struct hymo_entry *entry;
    struct hymo_hide_entry *hide_entry;
    struct hymo_inject_entry *inject_entry;
    struct hymo_xattr_sb_entry *sb_entry;
    struct hymo_merge_entry *merge_entry;
    struct hlist_node *tmp;
    int bkt;
    hash_for_each_safe(hymo_paths, bkt, tmp, entry, node) {
        hash_del(&entry->node);
        hash_del(&entry->target_node);
        kfree(entry->src);
        kfree(entry->target);
        kfree(entry);
    }
    hash_for_each_safe(hymo_hide_paths, bkt, tmp, hide_entry, node) {
        hash_del(&hide_entry->node);
        kfree(hide_entry->path);
        kfree(hide_entry);
    }
    hash_for_each_safe(hymo_inject_dirs, bkt, tmp, inject_entry, node) {
        hash_del(&inject_entry->node);
        kfree(inject_entry->dir);
        kfree(inject_entry);
    }
    hash_for_each_safe(hymo_xattr_sbs, bkt, tmp, sb_entry, node) {
        hash_del(&sb_entry->node);
        kfree(sb_entry);
    }
    hash_for_each_safe(hymo_merge_dirs, bkt, tmp, merge_entry, node) {
        hash_del(&merge_entry->node);
        kfree(merge_entry->src);
        kfree(merge_entry->target);
        kfree(merge_entry);
    }
}

static void hymofs_add_inject_rule(char *dir)
{
    struct hymo_inject_entry *inject_entry;
    u32 hash;
    bool found = false;

    if (!dir) return;

    hash = full_name_hash(NULL, dir, strlen(dir));
    hash_for_each_possible(hymo_inject_dirs, inject_entry, node, hash) {
        if (strcmp(inject_entry->dir, dir) == 0) {
            found = true;
            break;
        }
    }
    if (!found) {
        inject_entry = kmalloc(sizeof(*inject_entry), GFP_ATOMIC);
        if (inject_entry) {
            inject_entry->dir = dir;
            hash_add(hymo_inject_dirs, &inject_entry->node, hash);
            hymo_log("auto-inject parent: %s\n", dir);
        } else {
            kfree(dir);
        }
    } else {
        kfree(dir);
    }
}

static void hymofs_reorder_mnt_id(void)
{
    struct mnt_namespace *ns = current->nsproxy->mnt_ns;
    struct mount *m;
    int id = 1;
    bool is_hymo_mount;
    
    if (ns && !list_empty(&ns->list)) {
        struct mount *first = list_first_entry(&ns->list, struct mount, mnt_list);
        if (first->mnt_id < 500000) id = first->mnt_id;
    }

    if (!ns) return;

    list_for_each_entry(m, &ns->list, mnt_list) {
        is_hymo_mount = false;
        
        if (m->mnt_devname && (
            strcmp(m->mnt_devname, hymo_current_mirror_path) == 0 || 
            strcmp(m->mnt_devname, hymo_current_mirror_name) == 0
        )) {
            is_hymo_mount = true;
        }

        if (is_hymo_mount && hymo_stealth_enabled) {
            if (m->mnt_id < 500000) {
#ifdef CONFIG_KSU_SUSFS
                WRITE_ONCE(m->mnt.susfs_mnt_id_backup, m->mnt_id);
#endif
                WRITE_ONCE(m->mnt_id, 500000 + (id % 1000));
            }
        } else {
            if (m->mnt_id >= 500000) continue;
            
#ifdef CONFIG_KSU_SUSFS
            WRITE_ONCE(m->mnt.susfs_mnt_id_backup, m->mnt_id);
#endif
            WRITE_ONCE(m->mnt_id, id++);
        }
    }
}

static void hymofs_spoof_mounts(void)
{
    struct mnt_namespace *ns = current->nsproxy->mnt_ns;
    struct mount *m;
    char *system_devname = NULL;
    struct path sys_path;

    if (!ns) return;
    if (!hymo_stealth_enabled) return;

    if (kern_path("/system", LOOKUP_FOLLOW, &sys_path) == 0) {
        struct mount *sys_mnt = real_mount(sys_path.mnt);
        if (sys_mnt && sys_mnt->mnt_devname) {
            system_devname = kstrdup(sys_mnt->mnt_devname, GFP_KERNEL);
        }
        path_put(&sys_path);
    }
    
    if (!system_devname) {
        if (kern_path("/", LOOKUP_FOLLOW, &sys_path) == 0) {
            struct mount *sys_mnt = real_mount(sys_path.mnt);
            if (sys_mnt && sys_mnt->mnt_devname) {
                system_devname = kstrdup(sys_mnt->mnt_devname, GFP_KERNEL);
            }
            path_put(&sys_path);
        }
    }

    if (!system_devname) return;

    list_for_each_entry(m, &ns->list, mnt_list) {
        if (m->mnt_devname && (
            strcmp(m->mnt_devname, hymo_current_mirror_path) == 0 || 
            strcmp(m->mnt_devname, hymo_current_mirror_name) == 0
        )) {
            const char *old_name = m->mnt_devname;
            m->mnt_devname = kstrdup(system_devname, GFP_KERNEL);
            if (m->mnt_devname) {
                kfree_const(old_name);
            } else {
                m->mnt_devname = old_name;
            }
        }
    }
    kfree(system_devname);
}

static int hymo_dispatch_cmd(unsigned int cmd, void __user *arg) {
    struct hymo_syscall_arg req;
    struct hymo_entry *entry;
    struct hymo_hide_entry *hide_entry;
    struct hymo_inject_entry *inject_entry;
    char *src = NULL, *target = NULL;
    u32 hash;
    unsigned long flags;
    bool found = false;
    int ret = 0;

    if (cmd == HYMO_CMD_CLEAR_ALL) {
        spin_lock_irqsave(&hymo_lock, flags);
        hymo_cleanup();
        strscpy(hymo_mirror_path_buf, HYMO_DEFAULT_MIRROR_PATH, PATH_MAX);
        strscpy(hymo_mirror_name_buf, HYMO_DEFAULT_MIRROR_NAME, NAME_MAX);
        hymo_current_mirror_path = hymo_mirror_path_buf;
        hymo_current_mirror_name = hymo_mirror_name_buf;
        atomic_inc(&hymo_atomiconfig);
        spin_unlock_irqrestore(&hymo_lock, flags);
        return 0;
    }
    
    if (cmd == HYMO_CMD_GET_VERSION) {
        return HYMO_PROTOCOL_VERSION;
    }

    if (cmd == HYMO_CMD_SET_DEBUG) {
        int val;
        if (copy_from_user(&val, arg, sizeof(val))) return -EFAULT;
        hymo_debug_enabled = !!val;
        hymo_log("debug mode %s\n", hymo_debug_enabled ? "enabled" : "disabled");
        return 0;
    }

    if (cmd == HYMO_CMD_REORDER_MNT_ID) {
        hymofs_spoof_mounts();
        hymofs_reorder_mnt_id();
        return 0;
    }

    if (cmd == HYMO_CMD_SET_STEALTH) {
        int val;
        if (copy_from_user(&val, arg, sizeof(val))) return -EFAULT;
        hymo_stealth_enabled = !!val;
        hymo_log("stealth mode %s\n", hymo_stealth_enabled ? "enabled" : "disabled");
        if (hymo_stealth_enabled) {
            hymofs_spoof_mounts();
            hymofs_reorder_mnt_id();
        }
        return 0;
    }

    if (copy_from_user(&req, arg, sizeof(req))) return -EFAULT;

    if (cmd == HYMO_CMD_SET_MIRROR_PATH) {
        char *new_path = NULL;
        char *new_name = NULL;
        
        if (req.src) {
            new_path = strndup_user(req.src, PATH_MAX);
            if (IS_ERR(new_path)) return PTR_ERR(new_path);
        } else {
            return -EINVAL;
        }

        hymo_log("setting mirror path to: %s\n", new_path);

        char *slash = strrchr(new_path, '/');
        if (slash) {
            new_name = kstrdup(slash + 1, GFP_KERNEL);
        } else {
            new_name = kstrdup(new_path, GFP_KERNEL);
        }

        if (!new_name) {
            kfree(new_path);
            return -ENOMEM;
        }

        spin_lock_irqsave(&hymo_lock, flags);
        strscpy(hymo_mirror_path_buf, new_path, PATH_MAX);
        strscpy(hymo_mirror_name_buf, new_name, NAME_MAX);
        hymo_current_mirror_path = hymo_mirror_path_buf;
        hymo_current_mirror_name = hymo_mirror_name_buf;
        spin_unlock_irqrestore(&hymo_lock, flags);

        kfree(new_path);
        kfree(new_name);
        return 0;
    }

    if (req.src) {
        src = strndup_user(req.src, PAGE_SIZE);
        if (IS_ERR(src)) return PTR_ERR(src);
    }
    if (req.target) {
        target = strndup_user(req.target, PAGE_SIZE);
        if (IS_ERR(target)) {
            kfree(src);
            return PTR_ERR(target);
        }
    }

    switch (cmd) {
        case HYMO_CMD_ADD_MERGE_RULE: {
            struct hymo_merge_entry *merge_entry;
            if (!src || !target) { ret = -EINVAL; break; }
            
            hymo_log("add merge rule: src=%s, target=%s\n", src, target);
            
            hash = full_name_hash(NULL, src, strlen(src));
            spin_lock_irqsave(&hymo_lock, flags);
            
            hash_for_each_possible(hymo_merge_dirs, merge_entry, node, hash) {
                if (strcmp(merge_entry->src, src) == 0 && strcmp(merge_entry->target, target) == 0) {
                    found = true;
                    break;
                }
            }
            
            if (!found) {
                merge_entry = kmalloc(sizeof(*merge_entry), GFP_ATOMIC);
                if (merge_entry) {
                    merge_entry->src = src;
                    merge_entry->target = target;
                    hash_add(hymo_merge_dirs, &merge_entry->node, hash);
                    
                    {
                        struct hymo_inject_entry *inj;
                        bool inj_found = false;
                        hash_for_each_possible(hymo_inject_dirs, inj, node, hash) {
                            if (strcmp(inj->dir, src) == 0) {
                                inj_found = true;
                                break;
                            }
                        }
                        if (!inj_found) {
                            inj = kmalloc(sizeof(*inj), GFP_ATOMIC);
                            if (inj) {
                                inj->dir = kstrdup(src, GFP_ATOMIC);
                                if (inj->dir) hash_add(hymo_inject_dirs, &inj->node, hash);
                                else kfree(inj);
                            }
                        }
                    }
                    
                    src = NULL;
                    target = NULL;
                    hymofs_add_inject_rule(kstrdup(merge_entry->src, GFP_ATOMIC));
                } else {
                    ret = -ENOMEM;
                }
            } else {
                ret = -EEXIST;
            }
            atomic_inc(&hymo_atomiconfig);
            spin_unlock_irqrestore(&hymo_lock, flags);
            break;
        }

        case HYMO_CMD_ADD_RULE: {
            char *parent_dir = NULL;
            char *resolved_src = NULL;
            struct path path;
            char *tmp_buf = kmalloc(PATH_MAX, GFP_KERNEL);
            
            if (!src || !target) { 
                kfree(tmp_buf);
                ret = -EINVAL; 
                break; 
            }
            if (!tmp_buf) { ret = -ENOMEM; break; }

            hymo_log("add rule: src=%s, target=%s, type=%d\n", src, target, req.type);
            
            if (kern_path(src, LOOKUP_FOLLOW, &path) == 0) {
                char *res = d_path(&path, tmp_buf, PATH_MAX);
                if (!IS_ERR(res)) {
                    resolved_src = kstrdup(res, GFP_KERNEL);
                    
                    {
                        char *last_slash = strrchr(res, '/');
                        if (last_slash) {
                            if (last_slash == res) {
                                parent_dir = kstrdup("/", GFP_KERNEL);
                            } else {
                                size_t len = last_slash - res;
                                parent_dir = kmalloc(len + 1, GFP_KERNEL);
                                if (parent_dir) {
                                    memcpy(parent_dir, res, len);
                                    parent_dir[len] = '\0';
                                }
                            }
                        }
                    }
                }
                path_put(&path);
            } else {
                char *last_slash = strrchr(src, '/');
                if (last_slash && last_slash != src) {
                    size_t len = last_slash - src;
                    char *p_str = kmalloc(len + 1, GFP_KERNEL);
                    if (p_str) {
                        memcpy(p_str, src, len);
                        p_str[len] = '\0';
                        
                        if (kern_path(p_str, LOOKUP_FOLLOW, &path) == 0) {
                            char *res = d_path(&path, tmp_buf, PATH_MAX);
                            if (!IS_ERR(res)) {
                                size_t res_len = strlen(res);
                                size_t name_len = strlen(last_slash);
                                resolved_src = kmalloc(res_len + name_len + 1, GFP_KERNEL);
                                if (resolved_src) {
                                    strcpy(resolved_src, res);
                                    strcat(resolved_src, last_slash);
                                }
                                parent_dir = kstrdup(res, GFP_KERNEL);
                            }
                            path_put(&path);
                        }
                        kfree(p_str);
                    }
                }
            }
            
            kfree(tmp_buf);

            if (resolved_src) {
                kfree(src);
                src = resolved_src;
            }

            hash = full_name_hash(NULL, src, strlen(src));
            spin_lock_irqsave(&hymo_lock, flags);

            {
                hash_for_each_possible(hymo_paths, entry, node, hash) {
                    if (strcmp(entry->src, src) == 0) {
                        hash_del(&entry->target_node);
                        kfree(entry->target);
                        entry->target = kstrdup(target, GFP_ATOMIC);
                        entry->type = req.type;
                        if (entry->target)
                            hash_add(hymo_targets, &entry->target_node, full_name_hash(NULL, entry->target, strlen(entry->target)));
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    entry = kmalloc(sizeof(*entry), GFP_ATOMIC);
                    if (entry) {
                        entry->src = kstrdup(src, GFP_ATOMIC);
                        entry->target = kstrdup(target, GFP_ATOMIC);
                        entry->type = req.type;
                        if (entry->src && entry->target) {
                            hash_add(hymo_paths, &entry->node, hash);
                            hash_add(hymo_targets, &entry->target_node, full_name_hash(NULL, entry->target, strlen(entry->target)));
                        } else {
                            kfree(entry->src);
                            kfree(entry->target);
                            kfree(entry);
                        }
                    }
                }
            }

            if (parent_dir) {
                hymofs_add_inject_rule(parent_dir);
            }

            atomic_inc(&hymo_atomiconfig);
            spin_unlock_irqrestore(&hymo_lock, flags);
            break;
        }

        case HYMO_CMD_HIDE_RULE: {
            char *resolved_src = NULL;
            struct path path;
            char *tmp_buf = kmalloc(PATH_MAX, GFP_KERNEL);

            if (!src) { 
                kfree(tmp_buf);
                ret = -EINVAL; 
                break; 
            }
            if (!tmp_buf) { ret = -ENOMEM; break; }

            hymo_log("hide rule: src=%s\n", src);

            if (kern_path(src, LOOKUP_FOLLOW, &path) == 0) {
                char *res = d_path(&path, tmp_buf, PATH_MAX);
                if (!IS_ERR(res)) {
                    resolved_src = kstrdup(res, GFP_KERNEL);
                }
                path_put(&path);
            }
            kfree(tmp_buf);

            if (resolved_src) {
                kfree(src);
                src = resolved_src;
            }

            hash = full_name_hash(NULL, src, strlen(src));
            spin_lock_irqsave(&hymo_lock, flags);
            hash_for_each_possible(hymo_hide_paths, hide_entry, node, hash) {
                if (strcmp(hide_entry->path, src) == 0) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                hide_entry = kmalloc(sizeof(*hide_entry), GFP_ATOMIC);
                if (hide_entry) {
                    hide_entry->path = kstrdup(src, GFP_ATOMIC);
                    if (hide_entry->path)
                        hash_add(hymo_hide_paths, &hide_entry->node, hash);
                    else
                        kfree(hide_entry);
                }
            }
            atomic_inc(&hymo_atomiconfig);
            spin_unlock_irqrestore(&hymo_lock, flags);
            break;
        }

        case HYMO_CMD_HIDE_OVERLAY_XATTRS: {
            struct path path;
            struct hymo_xattr_sb_entry *sb_entry;
            bool found = false;
            
            if (!src) { ret = -EINVAL; break; }
            
            if (kern_path(src, LOOKUP_FOLLOW, &path) == 0) {
                struct super_block *sb = path.dentry->d_sb;
                
                spin_lock_irqsave(&hymo_lock, flags);
                hash_for_each_possible(hymo_xattr_sbs, sb_entry, node, (unsigned long)sb) {
                    if (sb_entry->sb == sb) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    sb_entry = kmalloc(sizeof(*sb_entry), GFP_ATOMIC);
                    if (sb_entry) {
                        sb_entry->sb = sb;
                        hash_add(hymo_xattr_sbs, &sb_entry->node, (unsigned long)sb);
                        hymo_log("hide xattrs for sb %p (path: %s)\n", sb, src);
                    }
                }
                atomic_inc(&hymo_atomiconfig);
                spin_unlock_irqrestore(&hymo_lock, flags);
                path_put(&path);
            } else {
                ret = -ENOENT;
            }
            break;
        }

        case HYMO_CMD_DEL_RULE:
            if (!src) { ret = -EINVAL; break; }
            hymo_log("del rule: src=%s\n", src);
            hash = full_name_hash(NULL, src, strlen(src));
            spin_lock_irqsave(&hymo_lock, flags);
            
            hash_for_each_possible(hymo_paths, entry, node, hash) {
                if (strcmp(entry->src, src) == 0) {
                    hash_del(&entry->node);
                    hash_del(&entry->target_node);
                    kfree(entry->src);
                    kfree(entry->target);
                    kfree(entry);
                    goto out_delete;
                }
            }
            hash_for_each_possible(hymo_hide_paths, hide_entry, node, hash) {
                if (strcmp(hide_entry->path, src) == 0) {
                    hash_del(&hide_entry->node);
                    kfree(hide_entry->path);
                    kfree(hide_entry);
                    goto out_delete;
                }
            }
            hash_for_each_possible(hymo_inject_dirs, inject_entry, node, hash) {
                if (strcmp(inject_entry->dir, src) == 0) {
                    hash_del(&inject_entry->node);
                    kfree(inject_entry->dir);
                    kfree(inject_entry);
                    goto out_delete;
                }
            }
    out_delete:
            atomic_inc(&hymo_atomiconfig);
            spin_unlock_irqrestore(&hymo_lock, flags);
            break;

        case HYMO_CMD_LIST_RULES: {
            struct hymo_syscall_list_arg list_arg;
            char *kbuf;
            size_t buf_size;
            size_t written = 0;
            int bkt;
            struct hymo_xattr_sb_entry *sb_entry;
            struct hymo_merge_entry *merge_entry;

            if (copy_from_user(&list_arg, (void __user *)arg, sizeof(list_arg))) {
                ret = -EFAULT;
                break;
            }

            buf_size = list_arg.size;
            if (buf_size > 128 * 1024) buf_size = 128 * 1024;
            
            kbuf = kzalloc(buf_size, GFP_KERNEL);
            if (!kbuf) {
                ret = -ENOMEM;
                break;
            }

            spin_lock_irqsave(&hymo_lock, flags);
            
            written += scnprintf(kbuf + written, buf_size - written, "HymoFS Protocol: %d\n", HYMO_PROTOCOL_VERSION);
            written += scnprintf(kbuf + written, buf_size - written, "HymoFS Atomiconfig Version: %d\n", atomic_read(&hymo_atomiconfig));

            hash_for_each(hymo_paths, bkt, entry, node) {
                if (written >= buf_size) break;
                written += scnprintf(kbuf + written, buf_size - written, "add %s %s %d\n", entry->src, entry->target, entry->type);
            }
            hash_for_each(hymo_hide_paths, bkt, hide_entry, node) {
                if (written >= buf_size) break;
                written += scnprintf(kbuf + written, buf_size - written, "hide %s\n", hide_entry->path);
            }
            hash_for_each(hymo_inject_dirs, bkt, inject_entry, node) {
                if (written >= buf_size) break;
                written += scnprintf(kbuf + written, buf_size - written, "inject %s\n", inject_entry->dir);
            }
            hash_for_each(hymo_merge_dirs, bkt, merge_entry, node) {
                if (written >= buf_size) break;
                written += scnprintf(kbuf + written, buf_size - written, "merge %s %s\n", merge_entry->src, merge_entry->target);
            }
            hash_for_each(hymo_xattr_sbs, bkt, sb_entry, node) {
                if (written >= buf_size) break;
                written += scnprintf(kbuf + written, buf_size - written, "hide_xattr_sb %p\n", sb_entry->sb);
            }
            spin_unlock_irqrestore(&hymo_lock, flags);

            if (copy_to_user(list_arg.buf, kbuf, written)) {
                ret = -EFAULT;
            } else {
                list_arg.size = written;
                if (copy_to_user((void __user *)arg, &list_arg, sizeof(list_arg))) {
                    ret = -EFAULT;
                }
            }
            
            kfree(kbuf);
            break;
        }

        case HYMO_CMD_REORDER_MNT_ID:
            hymo_log("reordering mount IDs\n");
            hymofs_reorder_mnt_id();
            break;

        case HYMO_CMD_SET_AVC_LOG_SPOOFING:
            if (req.type) {
                hymo_is_avc_log_spoofing_enabled = true;
                hymo_log("AVC log spoofing enabled\n");
            } else {
                hymo_is_avc_log_spoofing_enabled = false;
                hymo_log("AVC log spoofing disabled\n");
            }
            break;

        default:
            ret = -EINVAL;
            break;
    }

    kfree(src);
    kfree(target);
    return ret;
}

static int __init hymofs_init(void)
{
    spin_lock_init(&hymo_lock);
    hash_init(hymo_paths);
    hash_init(hymo_targets);
    hash_init(hymo_hide_paths);
    hash_init(hymo_inject_dirs);
    hash_init(hymo_xattr_sbs);
    
    if (hymo_dispatch_cmd_hook) {
        pr_err("HymoFS: hook already set?\n");
    } else {
        hymo_dispatch_cmd_hook = hymo_dispatch_cmd;
    }
    
    pr_info("HymoFS: initialized (Syscall Mode)\n");
    return 0;
}
fs_initcall(hymofs_init);

char *__hymofs_resolve_target(const char *pathname)
{
    unsigned long flags;
    struct hymo_entry *entry;
    struct hymo_merge_entry *merge_entry;
    u32 hash;
    char *target = NULL;
    const char *p;
    size_t path_len;
    struct list_head candidates;
    struct hymo_merge_target_node *cand, *tmp;

    if (atomic_read(&hymo_atomiconfig) == 0) return NULL;
    if (!pathname) return NULL;
    
    INIT_LIST_HEAD(&candidates);
    path_len = strlen(pathname);
    hash = full_name_hash(NULL, pathname, path_len);

    spin_lock_irqsave(&hymo_lock, flags);
    hash_for_each_possible(hymo_paths, entry, node, hash) {
        if (strcmp(entry->src, pathname) == 0) {
            target = kstrdup(entry->target, GFP_ATOMIC);
            hymo_log("redirect %s -> %s\n", pathname, target);
            spin_unlock_irqrestore(&hymo_lock, flags);
            return target;
        }
    }
    
    p = pathname + path_len;
    while (p > pathname) {
        while (p > pathname && *p != '/') p--;
        if (p == pathname && *p != '/') break;
        
        size_t current_len = p - pathname;
        if (current_len == 0) { 
             break;
        }
        
        hash = full_name_hash(NULL, pathname, current_len);
        hash_for_each_possible(hymo_merge_dirs, merge_entry, node, hash) {
            if (strlen(merge_entry->src) == current_len && 
                strncmp(merge_entry->src, pathname, current_len) == 0) {
                
                const char *suffix = pathname + current_len;
                if (suffix[0] == '\0' || strcmp(suffix, "/.") == 0 || strcmp(suffix, "/..") == 0) {
                    continue;
                }

                size_t target_len = strlen(merge_entry->target);
                size_t suffix_len = path_len - current_len;
                
                cand = kmalloc(sizeof(*cand), GFP_ATOMIC);
                if (cand) {
                    cand->target = kmalloc(target_len + suffix_len + 1, GFP_ATOMIC);
                    if (cand->target) {
                        strcpy(cand->target, merge_entry->target);
                        strcat(cand->target, suffix);
                        list_add_tail(&cand->list, &candidates);
                    } else {
                        kfree(cand);
                    }
                }
            }
        }

        if (!list_empty(&candidates)) {
            break;
        }
        
        if (p > pathname) p--;
    }
    
    spin_unlock_irqrestore(&hymo_lock, flags);
    
    list_for_each_entry_safe(cand, tmp, &candidates, list) {
        if (!target) {
            struct path p;
            if (kern_path(cand->target, LOOKUP_FOLLOW, &p) == 0) {
                path_put(&p);
                target = cand->target;
                cand->target = NULL;
                hymo_log("merge redirect %s -> %s\n", pathname, target);
            }
        }
        
        if (cand->target) kfree(cand->target);
        kfree(cand);
    }

    return target;
}
EXPORT_SYMBOL(__hymofs_resolve_target);

int __hymofs_reverse_lookup(const char *pathname, char *buf, size_t buflen)
{
    unsigned long flags;
    struct hymo_entry *entry;
    struct hymo_merge_entry *merge_entry;
    u32 hash;
    int bkt;
    int ret = -1;

    if (atomic_read(&hymo_atomiconfig) == 0) return -1;
    if (!pathname || !buf) return -1;

    hash = full_name_hash(NULL, pathname, strlen(pathname));

    spin_lock_irqsave(&hymo_lock, flags);
    
    hash_for_each_possible(hymo_targets, entry, target_node, hash) {
        if (strcmp(entry->target, pathname) == 0) {
            if (strscpy(buf, entry->src, buflen) < 0) ret = -ENAMETOOLONG;
            else ret = strlen(buf);
            goto out;
        }
    }

    hash_for_each(hymo_merge_dirs, bkt, merge_entry, node) {
        size_t target_len = strlen(merge_entry->target);
        if (strncmp(pathname, merge_entry->target, target_len) == 0) {
            if (pathname[target_len] == '/' || pathname[target_len] == '\0') {
                size_t src_len = strlen(merge_entry->src);
                size_t suffix_len = strlen(pathname) - target_len;
                
                if (src_len + suffix_len + 1 > buflen) {
                    ret = -ENAMETOOLONG;
                } else {
                    memcpy(buf, merge_entry->src, src_len);
                    memcpy(buf + src_len, pathname + target_len, suffix_len);
                    buf[src_len + suffix_len] = '\0';
                    ret = src_len + suffix_len;
                }
                goto out;
            }
        }
    }

out:
    spin_unlock_irqrestore(&hymo_lock, flags);
    return ret;
}
EXPORT_SYMBOL(__hymofs_reverse_lookup);

bool __hymofs_should_hide(const char *pathname, size_t len)
{
    unsigned long flags;
    struct hymo_hide_entry *entry;
    u32 hash;
    bool found = false;

    if (atomic_read(&hymo_atomiconfig) == 0) return false;
    if (!pathname) return false;

    if (uid_eq(current_uid(), GLOBAL_ROOT_UID)) return false;

    if (hymo_stealth_enabled) {
#ifdef CONFIG_HYMOFS_USE_KSU
        if (susfs_is_current_ksu_domain()) return false;
#endif
        size_t name_len = strlen(hymo_current_mirror_name);
        size_t path_len = strlen(hymo_current_mirror_path);

        if (len == name_len && strcmp(pathname, hymo_current_mirror_name) == 0) return true;
        if (len == path_len && strcmp(pathname, hymo_current_mirror_path) == 0) return true;
    }

    hash = full_name_hash(NULL, pathname, len);
    spin_lock_irqsave(&hymo_lock, flags);
    hash_for_each_possible(hymo_hide_paths, entry, node, hash) {
        if (strcmp(entry->path, pathname) == 0) {
#ifdef CONFIG_HYMOFS_USE_KSU
            if (susfs_is_current_ksu_domain()) {
                found = false;
                break;
            }
#endif
            found = true;
            hymo_log("hide %s\n", pathname);
            break;
        }
    }
    spin_unlock_irqrestore(&hymo_lock, flags);
    return found;
}
EXPORT_SYMBOL(__hymofs_should_hide);

bool __hymofs_should_spoof_mtime(const char *pathname)
{
    unsigned long flags;
    struct hymo_inject_entry *entry;
    u32 hash;
    bool found = false;

    if (atomic_read(&hymo_atomiconfig) == 0) return false;
    if (!pathname) return false;

#ifdef CONFIG_HYMOFS_USE_KSU
    if (susfs_is_current_ksu_domain()) return false;
#endif

    hash = full_name_hash(NULL, pathname, strlen(pathname));

    spin_lock_irqsave(&hymo_lock, flags);
    hash_for_each_possible(hymo_inject_dirs, entry, node, hash) {
        if (strcmp(entry->dir, pathname) == 0) {
            found = true;
            break;
        }
    }
    spin_unlock_irqrestore(&hymo_lock, flags);
    return found;
}
EXPORT_SYMBOL(__hymofs_should_spoof_mtime);

static bool __hymofs_should_replace(const char *pathname)
{
    unsigned long flags;
    struct hymo_entry *entry;
    u32 hash;
    bool found = false;

    if (atomic_read(&hymo_atomiconfig) == 0) return false;
    if (!pathname) return false;

#ifdef CONFIG_HYMOFS_USE_KSU
    if (susfs_is_current_ksu_domain()) return false;
#endif

    hash = full_name_hash(NULL, pathname, strlen(pathname));

    spin_lock_irqsave(&hymo_lock, flags);
    hash_for_each_possible(hymo_paths, entry, node, hash) {
        if (strcmp(entry->src, pathname) == 0) {
            found = true;
            break;
        }
    }
    spin_unlock_irqrestore(&hymo_lock, flags);
    return found;
}

struct hymo_merge_ctx {
    struct dir_context ctx;
    struct list_head *head;
    const char *dir_path;
};

static bool hymo_merge_filldir(struct dir_context *ctx, const char *name, int namlen,
		      loff_t offset, u64 ino, unsigned int d_type)
{
    struct hymo_merge_ctx *mctx = container_of(ctx, struct hymo_merge_ctx, ctx);
    struct hymo_name_list *item;

    if (namlen == 1 && name[0] == '.') return true;
    if (namlen == 2 && name[0] == '.' && name[1] == '.') return true;

    if (namlen == 8 && strncmp(name, ".replace", 8) == 0) return true;

    if (d_type == DT_CHR) {
        char *path = kasprintf(GFP_KERNEL, "%s/%.*s", mctx->dir_path, namlen, name);
        if (path) {
            struct kstat stat;
            struct path p;
            if (kern_path(path, LOOKUP_FOLLOW, &p) == 0) {
                if (vfs_getattr(&p, &stat, STATX_TYPE, AT_STATX_SYNC_AS_STAT) == 0) {
                    if (S_ISCHR(stat.mode) && stat.rdev == 0) {
                        path_put(&p);
                        kfree(path);
                        return true;
                    }
                }
                path_put(&p);
            }
            kfree(path);
        }
    }

    {
        struct hymo_name_list *pos;
        list_for_each_entry(pos, mctx->head, list) {
            if (strlen(pos->name) == namlen && strncmp(pos->name, name, namlen) == 0) {
                return true; 
            }
        }
    }

    item = kmalloc(sizeof(*item), GFP_KERNEL);
    if (item) {
        item->name = kstrndup(name, namlen, GFP_KERNEL);
        item->type = d_type;
        if (item->name) {
            list_add(&item->list, mctx->head);
        } else {
            kfree(item);
        }
    }
    return true;
}

int hymofs_populate_injected_list(const char *dir_path, struct dentry *parent, struct list_head *head)
{
    unsigned long flags;
    struct hymo_entry *entry;
    struct hymo_inject_entry *inject_entry;
    struct hymo_merge_entry *merge_entry;
    struct hymo_name_list *item;
    u32 hash;
    int bkt;
    bool should_inject = false;
    struct list_head merge_targets;
    struct hymo_merge_target_node *target_node, *tmp_node;
    size_t dir_len;
    
    if (atomic_read(&hymo_atomiconfig) == 0) return 0;
    if (!dir_path) return 0;

    INIT_LIST_HEAD(&merge_targets);
    dir_len = strlen(dir_path);
    hash = full_name_hash(NULL, dir_path, dir_len);

    spin_lock_irqsave(&hymo_lock, flags);
    
    hash_for_each_possible(hymo_inject_dirs, inject_entry, node, hash) {
        if (strcmp(inject_entry->dir, dir_path) == 0) {
            should_inject = true;
            break;
        }
    }
    
    hash_for_each_possible(hymo_merge_dirs, merge_entry, node, hash) {
        if (strcmp(merge_entry->src, dir_path) == 0) {
            target_node = kmalloc(sizeof(*target_node), GFP_ATOMIC);
            if (target_node) {
                target_node->target = kstrdup(merge_entry->target, GFP_ATOMIC);
                list_add_tail(&target_node->list, &merge_targets);
                should_inject = true;
            }
        }
    }

    if (should_inject) {
        hash_for_each(hymo_paths, bkt, entry, node) {
            if (strncmp(entry->src, dir_path, dir_len) == 0) {
                char *name = NULL;
                if (dir_len == 1 && dir_path[0] == '/') {
                    name = entry->src + 1;
                } else if (entry->src[dir_len] == '/') {
                    name = entry->src + dir_len + 1;
                }

                if (name && *name && strchr(name, '/') == NULL) {
                    bool exists = false;
                    struct hymo_name_list *pos;
                    list_for_each_entry(pos, head, list) {
                        if (strcmp(pos->name, name) == 0) {
                            exists = true;
                            break;
                        }
                    }

                    if (!exists) {
                        item = kmalloc(sizeof(*item), GFP_ATOMIC);
                        if (item) {
                            item->name = kstrdup(name, GFP_ATOMIC);
                            item->type = entry->type;
                            if (item->name) {
                                list_add(&item->list, head);
                            }
                            else kfree(item);
                        }
                    }
                }
            }
        }
    }

    spin_unlock_irqrestore(&hymo_lock, flags);

    list_for_each_entry_safe(target_node, tmp_node, &merge_targets, list) {
        if (target_node->target) {
            struct path path;
            hymo_log("processing merge target: %s\n", target_node->target);
            if (kern_path(target_node->target, LOOKUP_FOLLOW, &path) == 0) {
                const struct cred *cred = get_task_cred(&init_task);
                struct file *f = dentry_open(&path, O_RDONLY | O_DIRECTORY, cred);
                if (!IS_ERR(f)) {
                    struct hymo_merge_ctx mctx = {
                        .ctx.actor = hymo_merge_filldir,
                        .head = head,
                        .dir_path = target_node->target
                    };
                    iterate_dir(f, &mctx.ctx);
                    fput(f);
                } else {
                    hymo_log("failed to open merge target: %s (err=%ld)\n", target_node->target, PTR_ERR(f));
                }
                put_cred(cred);
                path_put(&path);
            } else {
                hymo_log("failed to resolve merge target: %s\n", target_node->target);
            }
            kfree(target_node->target);
        }
        kfree(target_node);
    }

    return 0;
}
EXPORT_SYMBOL(hymofs_populate_injected_list);

struct filename *hymofs_handle_getname(struct filename *result)
{
    char *target = NULL;

    if (IS_ERR(result)) return result;

    if (hymofs_should_hide(result->name)) {
        putname(result);
        return ERR_PTR(-ENOENT);
    } else {
        if (result->name[0] != '/') {
            char *buf = kmalloc(PAGE_SIZE, GFP_KERNEL);
            if (buf) {
                struct path pwd;
                spin_lock(&current->fs->lock);
                pwd = current->fs->pwd;
                path_get(&pwd);
                spin_unlock(&current->fs->lock);

                char *cwd = d_path(&pwd, buf, PAGE_SIZE);
                if (!IS_ERR(cwd)) {
                    int cwd_len = strlen(cwd);
                    const char *name = result->name;
                    
                    if (name[0] == '.' && name[1] == '/') {
                        name += 2;
                    }

                    int name_len = strlen(name);
                    
                    if (cwd != buf) {
                        memmove(buf, cwd, cwd_len + 1);
                        cwd = buf;
                    }

                    if (cwd_len + 1 + name_len < PAGE_SIZE) {
                        if (cwd_len > 0 && cwd[cwd_len - 1] != '/') {
                            strcat(cwd, "/");
                        }
                        strcat(cwd, name);
                        
                        target = hymofs_resolve_target(cwd);
                        
                        if (!target && strstr(name, "MonetCoolapk.apk")) {
                            hymo_log("getname failed: cwd='%s', name='%s', constructed='%s'\n", 
                                     cwd, name, cwd);
                        }
                    }
                }
                path_put(&pwd);
                kfree(buf);
            }
        }
        
        if (!target) {
            target = hymofs_resolve_target(result->name);
        }

        if (target) {
            putname(result);
            result = getname_kernel(target);
            kfree(target);
        }
    }
    return result;
}
EXPORT_SYMBOL(hymofs_handle_getname);

void __hymofs_prepare_readdir(struct hymo_readdir_context *ctx, struct file *file)
{
    ctx->file = file;
    ctx->path_buf = NULL;
    ctx->dir_path = NULL;
    ctx->dir_path_len = 0;
    INIT_LIST_HEAD(&ctx->merge_targets);
    ctx->is_replace_mode = false;

    ctx->path_buf = (char *)__get_free_page(GFP_KERNEL);
    if (ctx->path_buf && file && file->f_path.dentry) {
        char *p = d_path(&file->f_path, ctx->path_buf, PAGE_SIZE);
        if (!IS_ERR(p)) {
            int len = strlen(p);
            memmove(ctx->path_buf, p, len + 1);
            ctx->dir_path = ctx->path_buf;
            ctx->dir_path_len = len;
            hymo_log("readdir prepare: %s\n", ctx->dir_path);

            {
                unsigned long flags;
                struct hymo_merge_entry *entry;
                u32 hash = full_name_hash(NULL, ctx->dir_path, ctx->dir_path_len);
                
                spin_lock_irqsave(&hymo_lock, flags);
                hash_for_each_possible(hymo_merge_dirs, entry, node, hash) {
                    if (strcmp(entry->src, ctx->dir_path) == 0) {
                        struct hymo_merge_target_node *node = kmalloc(sizeof(*node), GFP_ATOMIC);
                        if (node) {
                            node->target = kstrdup(entry->target, GFP_ATOMIC);
                            list_add_tail(&node->list, &ctx->merge_targets);
                        }
                    }
                }
                spin_unlock_irqrestore(&hymo_lock, flags);

                if (!list_empty(&ctx->merge_targets)) {
                    struct hymo_merge_target_node *node;
                    list_for_each_entry(node, &ctx->merge_targets, list) {
                        char *replace_path = kasprintf(GFP_KERNEL, "%s/.replace", node->target);
                        if (replace_path) {
                            struct path path;
                            if (kern_path(replace_path, LOOKUP_FOLLOW, &path) == 0) {
                                ctx->is_replace_mode = true;
                                hymo_log("replace mode enabled for %s (found %s)\n", ctx->dir_path, replace_path);
                                path_put(&path);
                            }
                            kfree(replace_path);
                            if (ctx->is_replace_mode) break;
                        }
                    }
                }
            }
        } else {
            free_page((unsigned long)ctx->path_buf);
            ctx->path_buf = NULL;
        }
    }
}
EXPORT_SYMBOL(__hymofs_prepare_readdir);

void __hymofs_cleanup_readdir(struct hymo_readdir_context *ctx)
{
    struct hymo_merge_target_node *node, *tmp;
    if (ctx->path_buf) free_page((unsigned long)ctx->path_buf);
    list_for_each_entry_safe(node, tmp, &ctx->merge_targets, list) {
        kfree(node->target);
        kfree(node);
    }
}
EXPORT_SYMBOL(__hymofs_cleanup_readdir);

bool __hymofs_check_filldir(struct hymo_readdir_context *ctx, const char *name, int namlen)
{
    bool ret = false;

    if (ctx->is_replace_mode) {
        if (!(namlen == 1 && name[0] == '.') && 
            !(namlen == 2 && name[0] == '.' && name[1] == '.')) {
            return true;
        }
    }

    if (ctx->dir_path) {
        if (ctx->dir_path_len + 1 + namlen < PAGE_SIZE) {
            char *p = ctx->path_buf + ctx->dir_path_len;
            if (p > ctx->path_buf && p[-1] != '/') *p++ = '/';
            memcpy(p, name, namlen);
            p[namlen] = '\0';
            
            if (hymofs_should_hide(ctx->path_buf)) {
                hymo_log("hiding %s\n", ctx->path_buf);
                ret = true;
            }
            else if (__hymofs_should_replace(ctx->path_buf)) {
                hymo_log("hiding (replace source) %s\n", ctx->path_buf);
                ret = true;
            }
            else if (!list_empty(&ctx->merge_targets)) {
                struct hymo_merge_target_node *node;
                list_for_each_entry(node, &ctx->merge_targets, list) {
                    char *target_path = kasprintf(GFP_KERNEL, "%s/%s", node->target, name);
                    if (target_path) {
                        struct path path;
                        if (kern_path(target_path, LOOKUP_FOLLOW, &path) == 0) {
                            hymo_log("hiding (merge shadowed) %s\n", ctx->path_buf);
                            ret = true;
                            path_put(&path);
                        }
                        kfree(target_path);
                        if (ret) break;
                    }
                }
            }

            ctx->path_buf[ctx->dir_path_len] = '\0';
        }
    }
    return ret;
}
EXPORT_SYMBOL(__hymofs_check_filldir);

struct linux_dirent {
	unsigned long	d_ino;
	unsigned long	d_off;
	unsigned short	d_reclen;
	char		d_name[];
};

int hymofs_inject_entries(struct hymo_readdir_context *ctx, void __user **dir_ptr, int *count, loff_t *pos)
{
    struct linux_dirent __user *current_dir = *dir_ptr;
    struct list_head head;
    struct hymo_name_list *item, *tmp;
    loff_t current_idx = 0;
    loff_t start_idx;
    int injected = 0;
    int error = 0;
    int initial_count = *count;
    bool is_transition = (*pos < HYMO_MAGIC_POS);
    struct dentry *parent;

    if (!ctx->file) return 0;
    parent = ctx->file->f_path.dentry;

    if (is_transition) {
        start_idx = 0;
    } else {
        start_idx = *pos - HYMO_MAGIC_POS;
    }

    INIT_LIST_HEAD(&head);
    hymofs_populate_injected_list(ctx->dir_path, parent, &head);

    list_for_each_entry_safe(item, tmp, &head, list) {
        if (current_idx >= start_idx) {
            int name_len = strlen(item->name);
            int reclen = ALIGN(offsetof(struct linux_dirent, d_name) + name_len + 2, sizeof(long));
            if (*count >= reclen) {
                struct linux_dirent d;
                d.d_ino = 1;
                d.d_off = HYMO_MAGIC_POS + current_idx + 1;
                d.d_reclen = reclen;
                if (copy_to_user(current_dir, &d, offsetof(struct linux_dirent, d_name)) ||
                    copy_to_user(current_dir->d_name, item->name, name_len) ||
                    put_user(0, current_dir->d_name + name_len) ||
                    put_user(item->type, (char __user *)current_dir + reclen - 1)) {
                        error = -EFAULT;
                        break;
                }
                current_dir = (struct linux_dirent __user *)((char __user *)current_dir + reclen);
                *count -= reclen;
                injected++;
            } else {
                break;
            }
        }
        current_idx++;
        list_del(&item->list);
        kfree(item->name);
        kfree(item);
    }
    
    list_for_each_entry_safe(item, tmp, &head, list) {
        list_del(&item->list);
        kfree(item->name);
        kfree(item);
    }

    if (error == 0) {
        if (injected > 0) {
            if (is_transition) {
                *pos = HYMO_MAGIC_POS + injected;
            } else {
                *pos += injected;
            }
        }
        error = initial_count - *count;
    }
    
    *dir_ptr = current_dir;
    return error;
}
EXPORT_SYMBOL(hymofs_inject_entries);

int hymofs_inject_entries64(struct hymo_readdir_context *ctx, void __user **dir_ptr, int *count, loff_t *pos)
{
    struct linux_dirent64 __user *current_dir = *dir_ptr;
    struct list_head head;
    struct hymo_name_list *item, *tmp;
    loff_t current_idx = 0;
    loff_t start_idx;
    int injected = 0;
    int error = 0;
    int initial_count = *count;
    bool is_transition = (*pos < HYMO_MAGIC_POS);
    struct dentry *parent;

    if (!ctx->file) return 0;
    parent = ctx->file->f_path.dentry;

    if (is_transition) {
        start_idx = 0;
    } else {
        start_idx = *pos - HYMO_MAGIC_POS;
    }

    INIT_LIST_HEAD(&head);
    hymofs_populate_injected_list(ctx->dir_path, parent, &head);

    list_for_each_entry_safe(item, tmp, &head, list) {
        if (current_idx >= start_idx) {
            int name_len = strlen(item->name);
            int reclen = ALIGN(offsetof(struct linux_dirent64, d_name) + name_len + 1, sizeof(u64));
            if (*count >= reclen) {
                struct linux_dirent64 d;
                d.d_ino = 1;
                d.d_off = HYMO_MAGIC_POS + current_idx + 1;
                d.d_reclen = reclen;
                d.d_type = item->type;
                if (copy_to_user(current_dir, &d, offsetof(struct linux_dirent64, d_name)) ||
                    copy_to_user(current_dir->d_name, item->name, name_len) ||
                    put_user(0, current_dir->d_name + name_len)) {
                        error = -EFAULT;
                        break;
                }
                current_dir = (struct linux_dirent64 __user *)((char __user *)current_dir + reclen);
                *count -= reclen;
                injected++;
            } else {
                break;
            }
        }
        current_idx++;
        list_del(&item->list);
        kfree(item->name);
        kfree(item);
    }
    
    list_for_each_entry_safe(item, tmp, &head, list) {
        list_del(&item->list);
        kfree(item->name);
        kfree(item);
    }

    if (error == 0) {
        if (injected > 0) {
            if (is_transition) {
                *pos = HYMO_MAGIC_POS + injected;
            } else {
                *pos += injected;
            }
        }
        error = initial_count - *count;
    }
    
    *dir_ptr = current_dir;
    return error;
}
EXPORT_SYMBOL(hymofs_inject_entries64);

static dev_t __attribute__((unused)) get_dev_for_path(const char *path_str) {
    struct path path;
    dev_t dev = 0;
    if (kern_path(path_str, LOOKUP_FOLLOW, &path) == 0) {
        if (path.dentry && path.dentry->d_sb) {
            dev = path.dentry->d_sb->s_dev;
        }
        path_put(&path);
    }
    return dev;
}

extern char *d_absolute_path(const struct path *, char *, int);
void hymofs_spoof_stat(const struct path *path, struct kstat *stat)
{
    if (!hymo_stealth_enabled) return;
    if (atomic_read(&hymo_atomiconfig) == 0) return;

    char *buf = kmalloc(PAGE_SIZE, GFP_KERNEL);
    if (buf && path && path->dentry) {
        char *p = d_absolute_path(path, buf, PAGE_SIZE);
        if (!IS_ERR(p)) {
            char *virtual_buf = kmalloc(PAGE_SIZE, GFP_KERNEL);
            bool is_injected = false;
            
            if (virtual_buf) {
                if (__hymofs_reverse_lookup(p, virtual_buf, PAGE_SIZE) > 0) {
                    hymo_log("spoofing merge target %s -> %s\n", p, virtual_buf);
                    p = virtual_buf;
                    is_injected = true;
                }
            }

            if (is_injected) {
                char *last_slash = strrchr(p, '/');
                if (last_slash) {
                    if (last_slash == p) {
                        struct path parent_path;
                        if (kern_path("/", LOOKUP_FOLLOW, &parent_path) == 0) {
                            struct inode *inode = d_backing_inode(parent_path.dentry);
                            stat->uid = inode->i_uid;
                            stat->gid = inode->i_gid;
                            stat->dev = inode->i_sb->s_dev;
                            path_put(&parent_path);
                        }
                    } else {
                        *last_slash = '\0';
                        struct path parent_path;
                        if (kern_path(p, LOOKUP_FOLLOW, &parent_path) == 0) {
                            struct inode *inode = d_backing_inode(parent_path.dentry);
                            stat->uid = inode->i_uid;
                            stat->gid = inode->i_gid;
                            stat->dev = inode->i_sb->s_dev;
                            path_put(&parent_path);
                        } else {
                            if (strncmp(p, "/system/", 8) == 0 || 
                                strncmp(p, "/vendor/", 8) == 0 ||
                                strncmp(p, "/product/", 9) == 0 ||
                                strncmp(p, "/odm/", 5) == 0 ||
                                strncmp(p, "/apex/", 6) == 0) {
                                stat->uid = KUIDT_INIT(0);
                                stat->gid = KGIDT_INIT(0);
                            }
                        }
                        *last_slash = '/';
                    }
                }
                stat->ino ^= 0x48594D4F;
            }

            if (hymofs_should_spoof_mtime(p)) {
                hymo_log("spoofing stat for %s\n", p);
                ktime_get_real_ts64(&stat->mtime);
                stat->ctime = stat->mtime;
            }
            if (__hymofs_should_replace(p)) {
                stat->ino ^= 0x48594D4F;
                
                if (strncmp(p, "/system/", 8) == 0) {
                    stat->uid = KUIDT_INIT(0);
                    stat->gid = KGIDT_INIT(0);
                }
            }
            
            if (virtual_buf) kfree(virtual_buf);
        }
        kfree(buf);
    }
}
EXPORT_SYMBOL(hymofs_spoof_stat);

bool hymofs_is_overlay_xattr(struct dentry *dentry, const char *name)
{
    struct hymo_xattr_sb_entry *sb_entry;
    bool found = false;
    unsigned long flags;

    if (!name) return false;
    if (strncmp(name, "trusted.overlay.", 16) != 0) return false;
    
    if (!dentry) return false;

    spin_lock_irqsave(&hymo_lock, flags);
    hash_for_each_possible(hymo_xattr_sbs, sb_entry, node, (unsigned long)dentry->d_sb) {
        if (sb_entry->sb == dentry->d_sb) {
            found = true;
            break;
        }
    }
    spin_unlock_irqrestore(&hymo_lock, flags);
    
    return found;
}
EXPORT_SYMBOL(hymofs_is_overlay_xattr);

ssize_t hymofs_filter_xattrs(struct dentry *dentry, char *klist, ssize_t len)
{
    struct hymo_xattr_sb_entry *sb_entry;
    bool should_filter = false;
    unsigned long flags;
    char *p = klist;
    char *end = klist + len;
    char *out = klist;
    ssize_t new_len = 0;
    
    if (!dentry) return len;

    spin_lock_irqsave(&hymo_lock, flags);
    hash_for_each_possible(hymo_xattr_sbs, sb_entry, node, (unsigned long)dentry->d_sb) {
        if (sb_entry->sb == dentry->d_sb) {
            should_filter = true;
            break;
        }
    }
    spin_unlock_irqrestore(&hymo_lock, flags);

    if (!should_filter) return len;

    while (p < end) {
        size_t slen = strlen(p);
        if (strncmp(p, "trusted.overlay.", 16) != 0) {
            if (out != p)
                memmove(out, p, slen + 1);
            out += slen + 1;
            new_len += slen + 1;
        }
        p += slen + 1;
    }
    return new_len;
}
EXPORT_SYMBOL(hymofs_filter_xattrs);

#endif