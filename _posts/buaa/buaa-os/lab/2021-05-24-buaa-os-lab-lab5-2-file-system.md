---
layout: "post"
title: "「BUAA-OS-Lab」 Lab5-2 文件系统"
subtitle: "文件系统"
author: "roife"
date: 2021-05-24

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "C@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

> 感谢 @DDoSolitary 开源的实验代码提供的帮助

# 课上

现在 MOS 的代码中还没有创建文件的用户接口，因此下面需要实现这个接口。

## Exam

### 题目

实现函数 `user_create`：

```c
int user_create(char* path, int isdir);
```

其中 `path` 表示当前文件相对于根目录的路径，`isdir` 规定了需要创建的类型：
- 当 `isdir` 为 `0` 时，表示需要创建一个普通文件
- 当 `isdir` 为 `1` 时，表示需要创建一个目录

你需要在user/lib.h中添加相应的定义语句，并在user/file.c中进行实现。

样例说明：
- `user_create("/myfile", 0)` 可以在根目录下创建一个名为 `myfile` 的文件
- `user_create("/mydir", 1)` 可以在根目录下创建一个名为 `mydir的` 目录
- `user_create("/mydir/myfile", 0)` 可以在mydir目录下创建一个名为 `myfile` 的文件，当 `mydir` 目录不存在时该函数出错

当创建成功时你需要返回 `0`，其他情况需要返回一个负值代表出错。错误情况如下所示：
- 同一个目录下不能出现同名文件或同名目录（大小写敏感），否则返回 `-E_FILE_EXISTS`
- 当在非根目录下创建文件/目录时，如果出现指定目录不存在的情况，返回 `-E_DIR_NOT_EXIST`（需要在 `include/mmu.h` 中对这个新的错误类型进行定义，值为 `13`）
- 其他错误情况可以返回任意负值

注意：用户创建时必须使用IPC机制，使用其他方式无法得分！
保证一个目录下不会出现一个文件和一个文件夹同名的情况

### 分析

模仿已有的文件系统系统调用即可，就是要改的地方比较多。

#### 添加错误类型

```c
// include/error.h
#define E_DIR_NOT_EXIST    13

#define MAXERROR 13
```

```c
// include/mmu.h
#define E_DIR_NOT_EXIST    13

#define MAXERROR 13
```

#### 用户态部分

```c
// include/fs.h
#define FSREQ_CREATE    8

// ...

struct Fsreq_create {
    u_char req_path[MAXPATHLEN];
    u_int req_isdir;
};
```

```c
// user/file.c
int create(const char *path, int type) {
    int r;
    if ((r = fsipc_create(path, type)) < 0) return r;
    return 0;
}
```

```c
// user/lib.h
int fsipc_create(const char *, int);
int user_create(char *path, int isdir);
```

```c
// user/fsipc.c
int fsipc_create(const char *path, int isdir) {
    struct Fsreq_create *req = (struct Fsreq_create *)fsipcbuf;

    if (strlen(path) >= MAXPATHLEN) return -E_BAD_PATH;
    strcpy((char *)req->req_path, path);
    req->req_isdir = isdir;
    return fsipc(FSREQ_CREATE, req, 0, 0);
}
```

#### 文件系统部分

```c
// fs/serv.c
void serve_create(u_int envid, struct Fsreq_create *rq) {
    int r = file_create(rq->req_path, NULL, rq->req_isdir);
    ipc_send(envid, r, 0, 0);
}

// fs/serv.c 的 serve 函数中添加
case FSREQ_CREATE:
    serve_create(whom, (struct Fsreq_create *) REQVA);
    break;
```

```c
// fs/fs.h
int file_create(char *path, struct File **file, int isdir);
```

```c
// fs/fs.c
int file_create(char *path, struct File **file, int isdir) {
    char name[MAXNAMELEN];
    int r;
    struct File *dir, *f;

    if ((r = walk_path(path, &dir, &f, name)) == 0) return -E_FILE_EXISTS;
    if (r != -E_NOT_FOUND) return r;
    if (!dir) return -E_DIR_NOT_EXIST;

    if (dir_alloc_file(dir, &f) < 0) return r;

    strcpy((char *)f->f_name, name);
    f->f_type = isdir ? FTYPE_DIR : FTYPE_REG;

    if (file) *file = f;

    return 0;
}
```

## Extra

### Task 1

#### 题目

基于 exam 部分，为 `isdir` 增加取值：
- 当 `isdir` 为 `2` 时，表示需要创建一个普通文件。若中途有目录不存在，则沿途创建目录。
- 当 `isdir` 为 `3` 时，表示需要创建一个目录。若中途有目录不存在，则沿途创建目录。

#### 分析

沿途查找这个操作是在 `walk_path` 函数中实现的，所以可以在沿途查找的同时去创建对应的文件：

```c
// 增加查找到类型与是否创建文件
int walk_path(char *path, struct File **pdir, struct File **pfile, char *lastelem, u_int type, int createdir) {
    char *p;
    char name[MAXNAMELEN];
    struct File *dir, *file;
    int r;

    path = skip_slash(path);
    file = &super->s_root;
    dir = 0;
    name[0] = 0;

    if (pdir) {
        *pdir = 0;
    }

    *pfile = 0;

    while (*path != '\0') {
        dir = file;
        p = path;

        while (*path != '/' && *path != '\0') {
            path++;
        }

        if (path - p >= MAXNAMELEN) {
            return -E_BAD_PATH;
        }

        user_bcopy(p, name, path - p);
        name[path - p] = '\0';
        path = skip_slash(path);

        // 如果 path 已经到头了，就直接找要找的类型；否则找是否存在对应的路径
        if ((r = dir_lookup(dir, name, &file, *path ? FTYPE_DIR : type)) < 0) {
            if (r == -E_NOT_FOUND) {
                if (!*path) {
                    if (pdir) {
                        *pdir = dir;
                    }

                    if (lastelem) {
                        strcpy(lastelem, name);
                    }

                    *pfile = 0;
                } else if (createdir) { // 不存在路径，则沿途创建路径
                    if ((r = dir_alloc_file(dir, &file)) < 0) return r;
                    strcpy((char *)file->f_name, name);
                    file->f_type = FTYPE_DIR;
                    continue;
                }
            }

            return r;
        }
    }

    if (pdir) {
        *pdir = dir;
    }

    *pfile = file;
    return 0;
}
```

注意修改了 `walk_path`，也要修改文件中其他调用了 `walk_path` 的函数，如：

```c
if ((r = walk_path(path, 0, &f, 0)) < 0) {
    return r;
}
// 要变成
if ((r = walk_path(path, 0, &f, 0, FTYPE_REG, 0)) < 0) {
    return r;
}
```

最后修改原来创建文件的系统调用：

```c
// fs/fs.c
int file_create(char *path, struct File **file, int isdir) {
    char name[MAXNAMELEN];
    int r;
    struct File *dir, *f;

    int is_create_dir = (isdir == 1) || (isdir == 3); // 是否为创建路径
    int along = (isdir == 2) || (isdir == 3); // 是否沿途创建路径

    if ((r = walk_path(path, &dir, &f, name, is_create_dir, along)) == 0) return -E_FILE_EXISTS;
    if (r != -E_NOT_FOUND) return r;
    if (!dir) return -E_DIR_NOT_EXIST;

    if (dir_alloc_file(dir, &f) < 0) return r;

    strcpy((char *)f->f_name, name);
    f->f_type = is_create_dir ? FTYPE_DIR : FTYPE_REG;

    if (file) *file = f;

    return 0;
}
```

### Task 2

#### 题目

修改上面的代码，使得创建过程中允许同一目录下文件和子目录同名。

#### 分析

分析代码发现查找过程是使用 `dir_lookup` 这个函数实现的，所以想到给这个函数加一个参数表示要查找到类型，只有文件名和文件类型对应上了才算找到：

```c
int
dir_lookup(struct File *dir, char *name, struct File **file, int type) {
    int r;
    u_int i, j, nblock;
    struct File *f;

    nblock = dir->f_size / BY2BLK;

    for (i = 0; i < nblock; i++) {
        if ((r = file_get_block(dir, i, (void *) &f)) < 0) {
            return r;
        }

        for (j = 0; j < FILE2BLK; j++) {
            // 这里增加对于文件类型的判断
            if (!strcmp((char *)f[j].f_name, name) && f[j].f_type == type) {
                *file = &f[j];
                f[j].f_dir = dir;
                return 0;
            }
        }
    }

    return -E_NOT_FOUND;
}
```

注意还要在 `walk_path` 里面删掉这个判断：

```c
if (dir->f_type != FTYPE_DIR) return -E_NOT_FOUND;
```

这个判断语句表示如果找到的文件不是一个目录，那么就返回没找到。

但是在沿途创建的情况下，如果允许文件和目录同名，且当前目录中已有一个同名的文件，但是没有同名的目录时，应该继续创建目录而不是退出。而如果不是沿途创建，则会在 `dir_lookup` 中返回 `-E_NOT_FOUND` 的错误，因此也不会造成影响。