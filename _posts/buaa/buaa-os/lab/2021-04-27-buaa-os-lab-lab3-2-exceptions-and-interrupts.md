---
layout: "post"
title: "「BUAA-OS-Lab」 Lab3-2 中断和异常"
subtitle: "中断异常管理 & 进程调度"
author: "roife"
date: 2021-04-27

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "C@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 课上

下面的 exam 和 Extra 都不再采用时间片调度，还是按照优先级来调度。

假设 `env_pri` 由四部分组成：
- `0~7` 位：表示优先级
- `8~15` 位：表示 `func1`
- `16~23` 位：表示 `func2`
- `24~31` 位：表示 `func3`

为了方便，下面我先写了几个位运算用的函数：

```c
#define LOW_EIGHT_ONE 0xff

static u_int get_pri(struct Env *e) {
    return e->env_pri & LOW_EIGHT_ONE;
}

static u_int get_func1(struct Env *e) {
    return (e->env_pri >> 8) & LOW_EIGHT_ONE;
}

static u_int get_func2(struct Env *e) {
    return (e->env_pri >> 16) & LOW_EIGHT_ONE;
}

static u_int get_func3(struct Env *e) {
    return (e->env_pri >> 24) & LOW_EIGHT_ONE;
}

static u_int combine(u_int func3, u_int func2, u_int func1, u_int pri) {
    return (func3 << 24) + (func2 << 16) + (func1 << 8) + pri;
}
```

> **为什么这里要加 `static`？**
>
> `static` 关键字可以让这个函数仅在单文件中可见

## Exam

### Task 1

#### 题目

更改 `sched_yield`，不考虑时间片，只根据优先级 `pri` 进行调度。

#### 分析

首先观察到进程都是由 `env_create_priority` 创建的，而这个函数只会将进程放入 `env_sched_list[0]`，所以下面就不用考虑 `env_sched_list[1]`。

直接遍历链表，找到最大的然后运行即可。

```c
void sched_yield(void) {
    struct Env *nxtenv = NULL, *e;

    LIST_FOREACH(e, &env_sched_list[0], env_sched_link) {
        if (e->env_status == ENV_RUNNABLE && (nxtenv == NULL || get_pri(nxtenv) < get_pri(e))) {
            nxtenv = e;
        }
    }

    env_run(nxtenv ? nxtenv : curenv);
}
```

### Task 2

#### 题目

在 Task 1 的基础上，考虑更改进程的优先级。

每次中断切换进程时，会降低当前进程的优先级：
- 如果当前进程的 `func1` 为 0，则不更改优先级
- 如果当前进程的 `func1` 大于 0，则令当前进程的优先级减去 `func1`，即变成 `pri - func1`**（最多减少到 0）**

如果然后重复 Task 1 的任务调度。

#### 分析

直接做即可，需要注意的是这里的 `func` 和 `pri` 都是无符号数字，所以小心减法结果为负数时的溢出。

其他不变。

```c
void sched_yield(void) {
    struct Env *nxtenv = NULL, *e;

    if (curenv != NULL) {
        u_int func1 = get_func1(curenv);
        u_int func2 = get_func2(curenv);
        u_int func3 = get_func3(curenv);
        u_int pri = get_pri(curenv);
        if (func1 > 0) {
            curenv->env_pri = combine(func3, func2, func1, pri < func1 ? 0 : pri - func1);
        }
    }

    LIST_FOREACH(e, &env_sched_list[0], env_sched_link) {
        if (e->env_status == ENV_RUNNABLE &&
            (nxtenv == NULL || get_pri(nxtenv) < get_pri(e))) {
            nxtenv = e;
        }
    }

    env_run(nxtenv ? nxtenv : curenv);
}
```

## Extra

### 题目

在 Task 1 的基础上（不考虑 Task 2），考虑定时暂停的进程。

假设每次切换进程的中断发生时，时间都会加一。对于进程 `e`，它会在 `func2` 的时间点变成 `ENV_NOT_RUNNABLE` 的状态，并且 `func3` 个时间后恢复成 `ENV_RUNNABLE`。

进行调度时，首先处理进程的暂停和恢复，然后再按照 Task 1 进行调度。

### 分析

考虑用一个 `flag` 数组记录有哪些进程被暂停了。

这里涉及到两个点：
- 为什么要用额外的数组 `flag`，而不直接扫描链表根据 `func2` 以及 `func2 + func3` 判断
  + 因为可能有进程一开始就是 `ENV_NOT_RUNNABLE`，你不能因为 `func2 + func3` 符合条件就给它恢复了
- 为什么恢复的进程不需要从数组中删除
  + 显然恢复的元素以后不会再用到了（时间点过了），所以删不删无所谓

```c
void sched_yield(void) {
    struct Env *nxtenv = NULL, *e;
    static int count = 0, cnt_flag = 0;
    static struct Env *flag[NENV] = {0};

    ++count;

    if (curenv != NULL && get_func2(curenv) == count) {
        flag[++cnt_flag] = curenv;
        curenv->env_status = ENV_NOT_RUNNABLE;
    }

    int i;
    for (i = 1; i <= cnt_flag; ++i) {
        if (count == get_func2(flag[i]) + get_func3(flag[i])) {
            flag[i]->env_status = ENV_RUNNABLE;
        }
    }

    LIST_FOREACH(e, &env_sched_list[0], env_sched_link) {
        if (e->env_status == ENV_RUNNABLE &&
            (nxtenv == NULL || get_pri(nxtenv) < get_pri(e))) {
            nxtenv = e;
        }
    }

    env_run(nxtenv ? nxtenv : curenv);
}
```