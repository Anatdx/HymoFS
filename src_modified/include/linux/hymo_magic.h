#ifndef _LINUX_HYMO_MAGIC_H
#define _LINUX_HYMO_MAGIC_H

#ifdef __KERNEL__
#include <linux/ioctl.h>
#include <linux/types.h>
#include <linux/bits.h>
#else
#include <sys/ioctl.h>
#include <stddef.h>
#endif

#define HYMO_MAGIC1 0x48594D4F // "HYMO"
#define HYMO_MAGIC2 0x524F4F54 // "ROOT"
#define HYMO_PROTOCOL_VERSION 8

/*
 * HymoFS inode marking bits (stored in inode->i_mapping->flags)
 * Using high bits to avoid conflict with kernel AS_* flags and SUSFS bits
 * SUSFS uses bits 33-39, we use 40+
 */
#ifdef __KERNEL__
#define AS_FLAGS_HYMO_HIDE 40
#define BIT_HYMO_HIDE BIT(40)
/* Marks a directory as containing hidden entries (for fast filldir skip) */
#define AS_FLAGS_HYMO_DIR_HAS_HIDDEN 41
#define BIT_HYMO_DIR_HAS_HIDDEN BIT(41)
#endif

// Command definitions (for syscall mode - legacy)
#define HYMO_CMD_ADD_RULE    0x48001
#define HYMO_CMD_DEL_RULE    0x48002
#define HYMO_CMD_HIDE_RULE   0x48003
#define HYMO_CMD_INJECT_RULE 0x48004
#define HYMO_CMD_CLEAR_ALL   0x48005
#define HYMO_CMD_GET_VERSION 0x48006
#define HYMO_CMD_LIST_RULES  0x48007
#define HYMO_CMD_SET_DEBUG   0x48008
#define HYMO_CMD_REORDER_MNT_ID 0x48009
#define HYMO_CMD_SET_STEALTH 0x48010
#define HYMO_CMD_HIDE_OVERLAY_XATTRS 0x48011
#define HYMO_CMD_ADD_MERGE_RULE 0x48012
#define HYMO_CMD_SET_AVC_LOG_SPOOFING 0x48013
#define HYMO_CMD_SET_MIRROR_PATH 0x48014

// Device path
#define HYMO_DEVICE_NAME "hymo"
#define HYMO_DEVICE_PATH "/dev/hymo"

struct hymo_syscall_arg {
    char *src;
    char *target;
    int type;
};

struct hymo_syscall_list_arg {
    char *buf;
    size_t size;
};

// ioctl definitions (for fd-based mode)
// Must be after struct definitions
#define HYMO_IOC_MAGIC 'H'
#define HYMO_IOC_ADD_RULE           _IOW(HYMO_IOC_MAGIC, 1, struct hymo_syscall_arg)
#define HYMO_IOC_DEL_RULE           _IOW(HYMO_IOC_MAGIC, 2, struct hymo_syscall_arg)
#define HYMO_IOC_HIDE_RULE          _IOW(HYMO_IOC_MAGIC, 3, struct hymo_syscall_arg)
#define HYMO_IOC_CLEAR_ALL          _IO(HYMO_IOC_MAGIC, 5)
#define HYMO_IOC_GET_VERSION        _IOR(HYMO_IOC_MAGIC, 6, int)
#define HYMO_IOC_LIST_RULES         _IOWR(HYMO_IOC_MAGIC, 7, struct hymo_syscall_list_arg)
#define HYMO_IOC_SET_DEBUG          _IOW(HYMO_IOC_MAGIC, 8, int)
#define HYMO_IOC_REORDER_MNT_ID     _IO(HYMO_IOC_MAGIC, 9)
#define HYMO_IOC_SET_STEALTH        _IOW(HYMO_IOC_MAGIC, 10, int)
#define HYMO_IOC_HIDE_OVERLAY_XATTRS _IOW(HYMO_IOC_MAGIC, 11, struct hymo_syscall_arg)
#define HYMO_IOC_ADD_MERGE_RULE     _IOW(HYMO_IOC_MAGIC, 12, struct hymo_syscall_arg)
#define HYMO_IOC_SET_AVC_LOG_SPOOFING _IOW(HYMO_IOC_MAGIC, 13, int)
#define HYMO_IOC_SET_MIRROR_PATH    _IOW(HYMO_IOC_MAGIC, 14, struct hymo_syscall_arg)

#endif /* _LINUX_HYMO_MAGIC_H */