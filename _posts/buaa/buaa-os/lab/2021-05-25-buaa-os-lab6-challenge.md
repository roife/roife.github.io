---
layout: "post"
title: "「BUAA-OS-Lab」 Lab6-Challenge 环境变量"
subtitle: "A better shell for MOS & 环境变量"
author: "roife"
date: 2021-06-27

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "C@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 概述

本人完成了 Lab6-Challenge 的挑战性任务，包括“后台运行”，“一行多命令”，“简单引号支持”，“`tree`/`mkdir`/`touch` 命令”，“清屏”，“彩色输出”，“历史命令”，“环境变量”，“cd 命令” 等任务。

# Easy

## 后台运行

### 测试程序

用一个很大的循环实现延迟等效果：

```c
// testhang
int N = 100000000, i;
for (i = 0; i < N; ++i);
fwritef(1, "\nFINISHED");
```

### 修改汇编代码

防止前台阻塞，直接忽略输入。

```mips
LEAF(sys_cgetc)
1:  lb  t0, 0x90000000
    // beqz    t0, 1b
    // nop
    move    v0,t0
    jr  ra
    nop
END(sys_cgetc)
```

### 修改 shell

用一个变量 `hang` 标记是否要后台运行。

```c
case '&':
    hang = 1;
    break;
```

顺便添加一个后台运行的反馈信息：

```c
if (hang) {
    writef("[%d] WAIT\t", child_envid);
    for (i=0; i<argc; ++i) writef("%s ", argv[i]);
    writef("\n");
}
```

并且需要修改代码防止阻塞，并在任务结束后输出提示信息。

```c
if (!hang) wait(r);
else {
    pid = fork();
    if (pid == 0) {
        wait(r);
        writef("\n[%d] DONE\t", r);
        for (i=0; i<argc; ++i) writef("%s ", argv[i]);
        // ...
    }
}
```

## 一行多命令

使用 `fork` 创建一个子进程执行已经识别的命令：

```c
case ';':
    if ((pid = fork()) == 0) {
        input_fd = output_fd = -1;
        goto runit;
    }
    argc = hang = rightpipe = 0;
    break;
```

## 简单引号支持

简单修改 token 的部分，识别到引号的时候一直前进直到遇到下一个引号。

```c
if (*s == '\"') {
    *p1 = ++s;
    while(*s && !(*s == '\"' && *(s-1) != '\\')) ++s;
    *s++ = 0;
    *p2 = s;
    return 'w';
}
```

## `tree`/`mkdir`/`touch`

### `tree`

编写一个 `walk` 函数，传入路径和层级数量，遍历给定路径的文件。

```c
void walk(char *path, int level, int rec) {
    int fd, n;
    struct File f, *dir;
    char new[MAXPATHLEN] = {0};

    if(rec == 0) return;
    if ((fd = open(path, O_RDONLY)) < 0) user_panic("open %s: %e", path, fd);

    while ((n = readn(fd, &f, sizeof f)) == sizeof f) {
        if (f.f_name[0]) {
            dir = &f;

            // 格式化输出
            printline(' ', level * 4, 0);
            fwritef(1, "|-- ");

            // 输出当前文件或目录
            if(dir->f_type == FTYPE_REG) fwritef(1, "%s\n", dir->f_name);
            else fwritef(1, LIGHT_BLUE(%s\n), dir->f_name);

            // 递归输出子目录
            if(dir->f_type == FTYPE_DIR) {
                // 拼接子目录路径
                strcpy(new, path);
                strcat(new, "/");
                strcat(new, f.f_name);
                walk(new, level + 1, rec - 1);
            }
        }
    }
}
```

对于嵌套的目录，使用递归的方式遍历。

输出时借助于层级数量来格式化输出结果。

```c
void printline(char r, int n, int ret) { // 输出指定数量的字符，用来实现缩进
    int i = 0;
    for(i = 0; i < n;i++) fwritef(1, "%c", r);
    if(ret) fwritef(1, "\n");
}
```

### `mkdir`

#### 文件系统 `create` 支持

加入课上实验做过的部分：

```c
// fsipc.c
int fsipc_create(const char *path, u_int type) {
    struct Fsreq_create *req = (struct Fsreq_create *) fsipcbuf;
    if (strlen(path) >= MAXPATHLEN) return -E_BAD_PATH;

    strcpy((char *) req->req_path, path);
    req->req_type = type;
    return fsipc(FSREQ_CREATE, req, 0, 0);
}
```

```c
// file.c
int create(const char *path, int type) {
    int r;
    if ((r = fsipc_create(path, type)) < 0) return r;
    return 0;
}
```

```c
// fs.h
#define FSREQ_CREATE    8
// ...
struct Fsreq_create {
    u_char req_path[MAXPATHLEN];
    u_int req_type;
};
```

```c
// serv.c
void serve_create(u_int envid, struct Fsreq_create *rq) {
    struct File *file;
    int r;

    char path[MAXPATHLEN];
    user_bcopy(rq->req_path, path, MAXPATHLEN);
    path[MAXPATHLEN - 1] = 0;

    r = file_create(path, &file);
    file->f_size = 0;
    file->f_type = rq->req_type;

    ipc_send(envid, r, 0, 0);
}
```

```c
// serve 函数
case FSREQ_CREATE:
    serve_create(whom, (struct Fsreq_create *) REQVA);
    break;
```

```c
// user/lib.h
int fsipc_create(const char *, int);
```

#### `mkdir`

利用 `create` 和 `FTYPE_DIR` 参数创建目录文件。

```c
if((r = create(curpath, FTYPE_DIR)) < 0){
    fwritef(1, "Directory %s Already Exists!\n", curpath);
    return;
}
```

### `touch`

类似于 `mkdir`，在 `create` 时用 `FTYPE_REG` 参数。

## 清屏

直接输出字符序列 `\x1b[2J\x1b[H`。

## 彩色输出

用类似于 `\033[32m` 实现绿色输出，类似可以实现其他颜色的输出。

用 `\033[1m` 可以实现加粗效果。

用 `\033[m` 表示颜色输出结束。

# Normal

## 历史命令

### 读取/写入历史文件 API

```c
void history_init();
void history_save(char *s);
int history_read(char (*cmd)[128]);
```

每次在 `readline` 开头处调用即可。

### 按键识别

```c
if (i >= 2 && buf[i-2] == 27 && buf[i-1] == 91 && buf[i] == 65) { // Up arrow key
    writef("%c%c%c", 27, 91, 66);
    for (i -= 2; i; --i) writef("\b \b");
    if (cmdi) strcpy(buf, cmds[--cmdi]);
    else strcpy(buf, cmds[cmdi]);
    writef("%s", buf);
    i = strlen(buf) - 1;
} else if (i >= 2 && buf[i-2] == 27 && buf[i-1] == 91 && buf[i] == 66) { // Down arrow key
    // ...
}
```

# Challenge：环境变量

## 实现原理

创建两个全局变量数组或者局部变量数组，用来模拟一个哈希表。

```c
#define MOD (1<<8)
static char name_table[MOD][64];
static char value_table[MOD][256];
static int is_readonly[MOD];
#undef MOD
```

通过变量名的字符串哈希来实现查找（哈希算法为比较常用的 `DJB Hash`）。

```c
u_int strhash(const char *str) {
   unsigned int hash = 5381;
   unsigned int i    = 0;
   while(*str) hash = ((hash << 5) + hash) + (*str++);
   return hash % ((1 << 8) - 1);
}
```

交互上使用系统调用对环境变量进行访问，根据不同的 `op` 进行不同的操作：

```c
int syscall_env_var(char *name, char *value, u_int op);
// 0 - create
// 1 - get
// 2 - set
// 3 - unset
// 4 - get list
// 5 - create readonly
```

实现的时候还需要自己添加错误类型：

```c
#define E_ENV_VAR_NOT_FOUND 13
#define E_ENV_VAR_READONLY 14
```

## `export`

作用为输出所有的环境变量。

实现时直接遍历整个哈希表，查询键不为空的组对，并且将其指针放在一个指针数组中。

## `set`/`unset`

作用为设置/取消环境变量。其中 `set` 支持 `-r` 指令，设置只读变量。

实现时直接调用上面实现的系统调用，根据返回值判断“不存在环境变量”/“环境变量只读”的情况。

## 修改 `echo`

```c
if (argv[i][0] == '$') {
    // 读取环境变量
    char value[128];
    syscall_env_var(&argv[i][1], value, 1);
    write(1, value, strlen(value));
} else {
    write(1, argv[i], strlen(argv[i]));
}
```

## 相关错误常量

# 其他

## cd 和 `getcwd` 支持

利用环境变量实现 `curpath` 记录当前路径，利用系统调用可以获取和设置当前路径，并封装一套 API：

```c
void curpath_init(char *path);
int curpath_get(char *path);
int curpath_set(char *path);
int curpath_get_parent(char *path);
```

当使用：
- `cd .`：不改变路径
- `cd ..`：返回上一级目录（若为根目录，则不再返回）
- `cd folder`：进入目录

对所有的命令都重写，加入 `curpath` 的获取。

如果传入的命令是一个以 `/` 开头的路径，则为绝对路径；否则为相对路径。

## `>>` 重定向支持

不仅仅是用于 `>>` 的支持，在操作历史中也要使用 append。

### shell 支持

首先加入语法识别：

```c
if (*s == '>' && *(s + 1) == '>') {
    *p1 = s;
    *s++ = 0;
    *s++ = 0;
    *p2 = s;
    return 'a';
}
```

然后在 `open` 的时候加入 `O_APP` 参数。

```c
if ((r = open(t, O_WRONLY | O_CREAT | O_APP)) < 0) user_panic(">> open failed");
```

### 修改文件系统相关

加入相关操作符的支持：

```c
// lib.h
#define O_APP        0x1000        /* append to file */

// file.c

int open(const char *path, int mode) {
    // ...
    int fdnum = fd2num(fd);
    if (mode & O_APP) seek(fdnum, size); // 将文件指针指到文件末尾
    return fdnum;
}
```

## 沿途创建目录

课上内容。

```c
int file_create(char *path, struct File **file) {
    int r;

    // create directory along the way
    // 沿途分割路径并创建目录
    char *p1 = path[0] == '/' ? path + 1 : 0;
    while (p1 && *p1) {
        while (*p1 && *p1 != '/') ++p1;
        if (!*p1 || !*(p1 + 1)) break;

        *p1 = '\0';

        struct File *dir;
        r = my_file_create(path, &dir);
        if (r < 0 && r != -E_FILE_EXISTS) return r;

        *p1++ = '/';

        dir->f_type = FTYPE_DIR;
    }

    return my_file_create(path, file);
}
```

## 自动加入 `.b`

```c
char prog_name[64];
int prog_name_len = strlen(argv[0]);

strcpy(prog_name, argv[0]);
strcat(prog_name, ".b");
prog_name_len += 2;
prog_name[prog_name_len] = '\0';
```

## 其他命令：`rm`

### `rm`

和创建文件大同小异。

```c
if ((r = remove(curpath)) < 0) {
    fwritef(1, "File %s Not Exists!\n", curpath);
    return;
}
```

## 修改 `exit` 加入 `close_all()`

```c
void exit(void) {
    close_all();
    syscall_env_destroy(0);
}
```

## 修复 ASID 问题

如果不修复 ASID 分配的问题，那么最多只能执行 30 条命令。

```c
static u_int asid_bitmap[2] = {0};

static u_int asid_alloc() {
    int i, index, inner;
    for (i = 0; i < 64; ++i) {
        index = i >> 5;
        inner = i & 31;
        if ((asid_bitmap[index] & (1 << inner)) == 0) {
            asid_bitmap[index] |= 1 << inner;
            return i;
        }
    }
    panic("too many process!");
}

static void asid_free(u_int i) {
    int index = i >> 5, inner = i & 31;
    asid_bitmap[index] &= ~(1 << inner);
}

u_int mkenvid(struct Env *e) {
    u_int idx = e - envs;
    u_int asid = asid_alloc();
    return (asid << (1 + LOG2NENV)) | (1 << LOG2NENV) | idx;
}
```

## 修改 `open` 支持 `O_CREAT`

```c
// Open the file.
if ((r = file_open((char *) path, &f)) < 0) {
    if (r == -E_NOT_FOUND && (rq->req_omode & O_CREAT)) {
        if ((r = file_create(path, &f)) < 0) return r;
        f->f_type = FTYPE_REG;
    } else if (r == -E_NOT_FOUND && (rq->req_omode & O_MKDIR)) {
        if ((r = file_create(path, &f)) < 0) return r;
        f->f_type = FTYPE_DIR;
    } else {
        ipc_send(envid, r, 0, 0);
        return;
    }
}
```