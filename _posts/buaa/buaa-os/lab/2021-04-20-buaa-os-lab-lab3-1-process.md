---
layout: "post"
title: "「BUAA-OS-Lab」 Lab3-1 进程管理"
subtitle: "进程管理"
author: "roife"
date: 2021-04-20

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "C@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 课上

## Exam

以下题目中如果要定义新的函数，需要在 `include/env.h` 中添加对应的函数声明。

### Task 1

#### 题目

实现一个自己的 `u_int fork(struct Env*e);` 函数。作用是传入一个进程的指针作为父进程，创建一个新的进程。

其中 `env_status`，`env_pgdir`，`env_cr3`，`env_pri` 和父进程相同。

`env_id` 设置为新的 `env_id`，`env_parent_id` 设置为父进程的 `env_id`。

#### 分析

记得 `LIST_REMOVE`。

```c
u_int fork(struct Env*e) {
    struct Env* new;

    new = LIST_first_son_id(&env_free_list);
    LIST_REMOVE(new, env_link);

    // copy properties
    new->env_status = e->env_status;
    new->env_pgdir = e->env_pgdir;
    new->env_cr3 = e->env_cr3;
    new->env_pri = e->env_pri;
    new->env_id = mkenvid(new);
    new->env_parent_id = e->env_id;

    return new->env_id;
}
```

### Task 2

#### 题目

使用 `fork` 创建进程时，定义传入的进程为父进程，创建的进程为子进程。

如果用一个进程创建了多个子进程，那么规定它的儿子们的顺序为其创建顺序。

编写一个 `void lab3_output(u_int env_id);` 函数，传入 `env_id`，输出对应进程的父亲、第一个儿子、前一个兄弟、后一个兄弟对应的 `env_id`。输出格式为 `printf("%08x %08x %08x %08x\n", ...);`

#### 分析

这里我用的是类似于链式前向星的结构，你也可以用数组实现。

为了方便将 `env_id` 转换成 `env*`，先定义一个宏：

```c
#define GETENV_ID(ENV_ID) (envs + ENVX((ENV_ID)))
```

在 `Env` 中新增四个成员，表示 `env_id`：
- `last_son_id`：表示最后一个儿子
- `pre_id`：表示前一个兄弟
- `nxt_id`：表示后一个兄弟
- `first_son_id`：表示第一个儿子

```c
struct Env {
    u_int last_son_id, pre_id, nxt_id, first_son_id;
    // ...
};
```

然后在 `fork` 里面建立关系。

这里要注意 `pre_id` 可能是 `0`，即当前儿子是第一个儿子，此时要特判一下。

```c
u_int fork(struct Env*e) {
    // ...

    // set link
    new->pre_id = e->last_son_id;
    if (new->pre_id != 0) GETENV_ID(new->pre_id)->nxt_id = new->env_id;

    new->nxt_id = new->last_son_id = 0;
    e->last_son_id = new->env_id;
    if(e->first_son_id == 0) e->first_son_id = new->env_id;

    return new->env_id;
}

void lab3_output(u_int env_id) {
    struct Env *e = GETENV_ID(env_id);
    printf("%08x %08x %08x %08x\n", e->env_parent_id, e->first_son_id, e->pre_id, e->nxt_id);
}
```

### Task 3

#### 题目

编写函数 `int lab3_get_sum(u_int env_id);`，传入一个进程的 `env_id`，输出以其为根的进程树中总共有多少进程。

#### 分析

递归 DFS 就好了，很简单～

```c
int lab3_get_sum(u_int env_id) {
    int ret = 1, i;
    struct Env *e = GETENV_ID(env_id);
    for(i = e->first_son_id; i; i = e->nxt_id) {
        e = GETENV_ID(i);
        ret += lab3_get_sum(i);
    }
    return ret;
}
```

## Extra

以下题目中如果要定义新的函数，需要在 `include/env.h` 中添加对应的函数声明。

### 题目

写一个函数 `void lab3_kill(u_int env_id);` 删除 `fork` 出来的进程。删除一个进程后，将其所有儿子**依次**添加到根结点上。

例如 `1` 有两个儿子 `2 3`。进程树中有一个子树 `x`，其儿子为 `8 9`，则删除 `x` 后，`1` 的儿子为 `2 3 8 9`（按顺序）。

删除后需要释放该进程，可以参考 `env_free` 的写法释放资源。

### 分析

建议先删除 `e` 本身，再移动儿子。主要判断 0 的情况（即不存在该结点的情况）。

`free` 的过程直接抄函数。由于我们的 `fork()` 没有分配页，所以 `free` 的时候不需要释放页。

```c
u_int get_root(u_int env_id) {
    struct Env *e;
    u_int par_id = env_id;
    do {
        e = GETENV_ID(par_id);
        par_id = e->env_parent_id;
    } while(par_id);
    return e->env_id;
}

void lab3_kill(u_int env_id) {
    struct Env *e = GETENV_ID(env_id);
    u_int root_id = get_root(env_id);
    struct Env *rt = GETENV_ID(root_id), *par = GETENV_ID(e->env_parent_id);

    // delete e
    if (e->pre_id != 0) GETENV_ID(e->pre_id)->nxt_id = e->nxt_id;
    if (e->nxt_id != 0) GETENV_ID(e->nxt_id)->pre_id = e->pre_id;
    if (par->last_son_id == e->env_id) par->last_son_id = e->pre_id;
    if (par->first_son_id == e->env_id) par->first_son_id = e->nxt_id;

    // move children, set parent
    if (e->first_son_id != 0) {
        struct Env *son = GETENV_ID(e->first_son_id);
        for(; son->nxt_id; son = GETENV_ID(son->nxt_id)) son->env_parent_id = root_id;

        // connect son with e's parent
        son = GETENV_ID(e->first_son_id);
        son->pre_id = par->last_son_id;
        if (pre->last_son_id != 0) GETENV_ID(pre->last_son_id)->nxt_id = son->env_id;
        par->last_son_id = e->last_son_id;
        if (par->first_son_id == 0) par->first_son_id = son->env_id;
    }

    // free
    e->env_pgdir = 0;
    e->env_cr3 = 0;
    e->last_son_id = e->nxt_id = e->pre_id = e->first_son_id = 0;
    e->env_status = ENV_FREE;
    LIST_INSERT_HEAD(&env_free_list, e, env_link);
}
```

### 测试

可以自己写一个辅助的测试函数（DFS 输出进程结构）：

```c
void lab3_print_tree(u_int env_id) {
    int i;
    struct Env *e = GETENV_ID(env_id);
    for(i = e->first; i; i = e->nxt_id) {
        e = GETENV_ID(i);
        printf("%u->%u\n", env_id, i);
        lab3_get_sum(i);
    }
}
```

## 反思

课上花了很多时间在调一个令人啼笑皆非的 BUG，导致 Extra 没做完，课后发现是自己测试代码写错了。

说明还是太浮躁了，希望下次引以为戒。

错误的测试代码：

```c
struct Env *e;
page_alloc(e, 0); // 应该是 page_alloc(&e, 0);
```
