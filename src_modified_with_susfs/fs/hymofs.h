#ifndef _LINUX_HYMOFS_H
#define _LINUX_HYMOFS_H

#include <linux/types.h>
#include <linux/list.h>
#include <linux/atomic.h>

#ifdef CONFIG_HYMOFS

#define HYMO_MAGIC_POS 0x7000000000000000ULL

#define HYMO_DEFAULT_MIRROR_NAME "hymo_mirror"
#define HYMO_DEFAULT_MIRROR_PATH "/dev/" HYMO_DEFAULT_MIRROR_NAME

struct hymo_merge_target_node {
    struct list_head list;
    char *target;
    struct dentry *target_dentry;  /* Cached dentry for fast lookup */
};

/* Bloom filter for merge target filenames - ultra fast O(1) check */
#define HYMO_BLOOM_BITS 10  /* 1024 bits = 128 bytes */
#define HYMO_BLOOM_SIZE (1 << HYMO_BLOOM_BITS)
#define HYMO_BLOOM_MASK (HYMO_BLOOM_SIZE - 1)

/* Hash table for merge target filenames - O(1) lookup */
#define HYMO_MERGE_HASH_BITS 6
#define HYMO_MERGE_HASH_SIZE (1 << HYMO_MERGE_HASH_BITS)

struct hymo_merge_file_entry {
    struct hlist_node node;
    char *name;
    int namlen;
};

struct hymo_readdir_context {
    struct file *file;
    char *path_buf;
    char *dir_path;
    int dir_path_len;
    bool entry_written;
    struct list_head merge_targets;
    bool is_replace_mode;
    bool dir_has_hidden;  /* Fast path: skip hide check if false */
    bool has_merge_files; /* Fast path: skip merge check if false */
    unsigned long bloom_filter[HYMO_BLOOM_SIZE / BITS_PER_LONG]; /* Bloom filter for merge filenames */
    struct hlist_head merge_files[HYMO_MERGE_HASH_SIZE]; /* Pre-built hash of merge target filenames */
};

extern atomic_t hymo_atomiconfig;

void __hymofs_prepare_readdir(struct hymo_readdir_context *ctx, struct file *file);
void __hymofs_cleanup_readdir(struct hymo_readdir_context *ctx);
bool __hymofs_check_filldir(struct hymo_readdir_context *ctx, const char *name, int namlen);
int hymofs_inject_entries(struct hymo_readdir_context *ctx, void __user **dir_ptr, int *count, loff_t *pos);
int hymofs_inject_entries64(struct hymo_readdir_context *ctx, void __user **dir_ptr, int *count, loff_t *pos);
void hymofs_spoof_stat(const struct path *path, struct kstat *stat);
ssize_t hymofs_filter_xattrs(struct dentry *dentry, char *klist, ssize_t len);
bool hymofs_is_overlay_xattr(struct dentry *dentry, const char *name);

struct hymo_name_list {
    char *name;
    unsigned char type;
    struct list_head list;
};

struct filename;
struct filename *hymofs_handle_getname(struct filename *result);
struct filename *hymofs_resolve_relative(int dfd, const char *name);

char *__hymofs_resolve_target(const char *pathname);
int __hymofs_reverse_lookup(const char *pathname, char *buf, size_t buflen);
bool __hymofs_should_hide(const char *pathname, size_t len);
bool __hymofs_should_spoof_mtime(const char *pathname);
int hymofs_populate_injected_list(const char *dir_path, struct dentry *parent, struct list_head *head);

/* Fast O(1) inode-based hide check - core function */
bool __hymofs_is_inode_hidden(struct inode *inode);

/* Inline wrapper with fast-path checks */
static __always_inline bool hymofs_is_inode_hidden(struct inode *inode)
{
    /* Fast path: NULL checks */
    if (unlikely(!inode || !inode->i_mapping))
        return false;
    
    /* Fast path: Root sees everything */
    if (uid_eq(current_uid(), GLOBAL_ROOT_UID))
        return false;
    
    /* Fast path: No rules loaded */
    if (atomic_read(&hymo_atomiconfig) == 0)
        return false;
    
    return __hymofs_is_inode_hidden(inode);
}

static inline void hymofs_prepare_readdir(struct hymo_readdir_context *ctx, struct file *file)
{
    ctx->path_buf = NULL;
    ctx->file = file;
    if (atomic_read(&hymo_atomiconfig) == 0) return;
    __hymofs_prepare_readdir(ctx, file);
}

static inline void hymofs_cleanup_readdir(struct hymo_readdir_context *ctx)
{
    if (ctx->path_buf) __hymofs_cleanup_readdir(ctx);
}

static inline bool hymofs_check_filldir(struct hymo_readdir_context *ctx, const char *name, int namlen)
{
    if (!ctx->path_buf) return false;
    return __hymofs_check_filldir(ctx, name, namlen);
}

static inline char *hymofs_resolve_target(const char *pathname)
{
    if (atomic_read(&hymo_atomiconfig) == 0) return NULL;
    return __hymofs_resolve_target(pathname);
}

static inline int hymofs_reverse_lookup(const char *pathname, char *buf, size_t buflen)
{
    if (atomic_read(&hymo_atomiconfig) == 0) return -1;
    return __hymofs_reverse_lookup(pathname, buf, buflen);
}

static inline bool hymofs_should_hide(const char *pathname)
{
    if (atomic_read(&hymo_atomiconfig) == 0) return false;
    /* Fast path: check for NULL or empty */
    if (!pathname || !*pathname) return false;
    return __hymofs_should_hide(pathname, strlen(pathname));
}

static inline bool hymofs_should_spoof_mtime(const char *pathname)
{
    if (atomic_read(&hymo_atomiconfig) == 0) return false;
    return __hymofs_should_spoof_mtime(pathname);
}

#else

struct hymo_readdir_context {};
static inline void hymofs_prepare_readdir(struct hymo_readdir_context *ctx, struct file *file) {}
static inline void hymofs_cleanup_readdir(struct hymo_readdir_context *ctx) {}
static inline bool hymofs_check_filldir(struct hymo_readdir_context *ctx, const char *name, int namlen) { return false; }
static inline int hymofs_inject_entries(struct hymo_readdir_context *ctx, void __user **dir_ptr, int *count, loff_t *pos) { return 0; }
static inline int hymofs_inject_entries64(struct hymo_readdir_context *ctx, void __user **dir_ptr, int *count, loff_t *pos) { return 0; }
static inline void hymofs_spoof_stat(const struct path *path, struct kstat *stat) {}
static inline ssize_t hymofs_filter_xattrs(struct dentry *dentry, char *klist, ssize_t len) { return len; }
static inline bool hymofs_is_overlay_xattr(struct dentry *dentry, const char *name) { return false; }

static inline struct filename *hymofs_handle_getname(struct filename *result) { return result; }
static inline struct filename *hymofs_resolve_relative(int dfd, const char *name) { return NULL; }
static inline char *hymofs_resolve_target(const char *pathname) { return NULL; }
static inline char *hymofs_reverse_lookup(const char *pathname) { return NULL; }
static inline bool hymofs_should_hide(const char *pathname) { return false; }
static inline bool hymofs_should_spoof_mtime(const char *pathname) { return false; }
static inline int hymofs_populate_injected_list(const char *dir_path, struct dentry *parent, struct list_head *head) { return 0; }
static inline bool hymofs_is_inode_hidden(struct inode *inode) { return false; }

#endif /* CONFIG_HYMOFS */

#endif /* _LINUX_HYMOFS_H */
