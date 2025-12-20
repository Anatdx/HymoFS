#ifndef _HYMOFS_IOCTL_H
#define _HYMOFS_IOCTL_H

#include <linux/ioctl.h>

#define HYMO_IOC_MAGIC 0xE0
#define HYMO_PROTOCOL_VERSION 6

struct hymo_ioctl_arg {
    char *src;
    char *target;
    int type;
};

#define HYMO_TYPE_REDIRECT 0
#define HYMO_TYPE_MERGE 1

#define HYMO_IOC_ADD_RULE    _IOW(HYMO_IOC_MAGIC, 1, struct hymo_ioctl_arg)
#define HYMO_IOC_DEL_RULE    _IOW(HYMO_IOC_MAGIC, 2, struct hymo_ioctl_arg)
#define HYMO_IOC_HIDE_RULE   _IOW(HYMO_IOC_MAGIC, 3, struct hymo_ioctl_arg)
#define HYMO_IOC_INJECT_RULE _IOW(HYMO_IOC_MAGIC, 4, struct hymo_ioctl_arg)
#define HYMO_IOC_CLEAR_ALL   _IO(HYMO_IOC_MAGIC, 5)
#define HYMO_IOC_GET_VERSION _IOR(HYMO_IOC_MAGIC, 6, int)

// Buffer size for listing rules
#define HYMO_LIST_BUF_SIZE 4096

struct hymo_ioctl_list_arg {
    char *buf;
    size_t size;
};

#define HYMO_IOC_LIST_RULES  _IOWR(HYMO_IOC_MAGIC, 7, struct hymo_ioctl_list_arg)
#define HYMO_IOC_SET_DEBUG   _IOW(HYMO_IOC_MAGIC, 8, int)
#define HYMO_IOC_REORDER_MNT_ID _IO(HYMO_IOC_MAGIC, 9)
#define HYMO_IOC_SET_STEALTH _IOW(HYMO_IOC_MAGIC, 10, int)
#define HYMO_IOC_HIDE_OVERLAY_XATTRS _IOW(HYMO_IOC_MAGIC, 11, struct hymo_ioctl_arg)
#define HYMO_IOC_ADD_MERGE_RULE _IOW(HYMO_IOC_MAGIC, 12, struct hymo_ioctl_arg)

#endif
