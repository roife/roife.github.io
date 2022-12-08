---
layout: "post"
title: "「BUAA-OS-Lab」 Lab4-2 fork"
subtitle: "从进程到简单的线程"
author: "roife"
date: 2021-05-10

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "C@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

> 感谢 @DDoSolitary 开源的实验代码提供的帮助

# 课上

## Exam

模仿 `fork` 实现线程创建。

先在 `user/lib.h` 里面声明两个新函数：

```c
int tfork(void);
u_int uget_sp(void);
```

### Task 1

#### 题目

实现函数 `user_getsp`，返回当前 `ROUNDDOWN(SP, BY2PG)` ，其中 `SP` 为 `$sp` 的内容（即栈指针地址）。

#### 分析

要获取寄存器的内容必须要通过汇编实现：

```mips
// user/entry.S
.globl uget_sp

uget_sp:
    li v0, 0xfffff000
    and v0, v0, sp
    jr ra
    nop
```

### Task 2

#### 题目

实现 `tfork` 函数创建线程，返回值规则与 `fork` 相同：
- `> 0` 返回值是子线程的 pid，当前执行上下文是父线程
- `= 0` 当前执行上下文是子线程
- `< 0` 创建线程失败，当前执行上下文是父线程

为了降低难度，要求如下（正常的线程机制也可以通过评测）：
- 类似 `fork`，父子线程从 `tfork` 执行后，各自独立继续执行
- 栈区可以互相独立，`data` 段与 `bss` 段的变量要共享，且不考虑除 `data`/`bss`/`text` 段及用户栈之外的空间的共享问题
- 注意用户栈的大小可能不止 4KB，需要自行获取当前用户栈的顶部指针位置
- 系统调用机制需要都能独立正常使用，且父子线程可以通过 IPC 进行同步或通信

#### 分析

可以发现 `tfork` 和 `fork` 的唯一区别在于共享内存区域，即 `duppage` 的部分，其余部分与 `fork` 完全一致。

因此这里用了一个 `tduppage`。（其实 `tduppage` 和 `duppage` 基本上也完全一致）

`tduppage` 和 `duppage` 的区别在于，在 `tfork` 中只有栈空间是 COW 的，所以只有当地址高于当前的栈指针时才加入 COW 权限，而非栈的部分则直接映射相同的地址，不需要 COW 机制。

```c
// user/fork.c
// tduppage 基本上与 duppage 一样
static void
tduppage(u_int envid, u_int pn, int cow_data) {
    u_int addr;
    u_int perm;

    addr = pn << PGSHIFT;
    perm = (*vpt)[pn] & 0xfff;
    if (addr >= uget_sp() && (perm & PTE_R) && !(perm & PTE_LIBRARY)) { // 区别在这里
        perm = (perm & ~PTE_R) | PTE_COW;
    }
    // ...
}

// tfork 基本上与 fork 一样
int tfork() {
    // ...
    for (i = 0; i < USTACKTOP; i += BY2PG) {
        if (((*vpd)[PDX(i)] & PTE_V) && ((*vpt)[VPN(i)] & PTE_V)) {
          tduppage(newenvid, VPN(i));
        }
    }
    // ...
}
```

## Extra

分别统计用户空间页面被动分配和写时分配的缺页中断次数。

### 题目

- 将 `Env` 结构体中的 `env_nop` 更名为 `env_pgout` 并用其统计用户空间页面被动分配的缺页中断次数
- 将 `Env` 结构体中的 `env_runs` 更名为 `env_pgcow` 并用其统计写时分配的缺页中断次数

保证不会溢出。

输出规则如下：
- 发生用户空间页面被动分配
  + 输出`printf("\nEnv:0x%x, va:0x%x, pgcow:%d, pgout:%d\n");`
  + `Env` 表示进程号，`va` 表示引发缺页中断的指令地址
- 发生写时分配
  + 输出`printf("\nEnv:0x%x, code:0x%x, pgcow:%d, pgout:%d\n");`
  + `Env` 表示进程号，`code` 表示引发缺页分配的指令编码
- 最后在 `env_destroy` 函数中输出三者信息
  + `printf("%08x envid\n", e->env_id);`
  + `printf("%08x pgfault_out\n", out);`：用户空间的页面被动分配`
  + `printf("%08x pgfault_cow\n", cow);`：写时复制

注意：更改 `Env` 结构体导致其占用空间大小发生变化，可能会使得编译器编译出非预期的指令并导致奇怪的现象，因此请不要随意改动Env结构体。

### 分析

首先按照题目说的在 `include/env.h` 中修改变量的名字。

在进程被分配时，需要初始化这两个变量的值：

```c
// lib/env.c
int env_alloc(struct Env **new, u_int parent_id) {
    // ...
    e->env_pgcow = 0;
    e->env_pgout = 0;
    // ...
}
```

然后考虑发生缺页中断（即需要输出）的时候是什么情况：
- 用户空间页面被动分配：此时就是正常的缺页中断，会调用 `pageout` 函数
  + 此时正在执行的指令地址位于传入的 `va`
- 写时分配：会调用 `page_fault_handler` 函数
  + 此时已经发生了异常，异常前的信息被保存在 Trapframe 中，即发生异常时的 PC 为 `tf->cp0_epc`，所以对应的指令为 `*(u_int *)tf->cp0_epc`（注意类型转换）

对于所有的情况，进程号一直都是 `curenv->env_id`。

```c
// mm/pmap.c
void pageout(int va, int context) {
    // ...
    printf("\nEnv:0x%x, va:0x%x, pgcow:%d, pgout:%d\n", curenv->env_id, va, curenv->env_pgcow, ++curenv->env_pgout);
}
```

```c
void page_fault_handler(struct Trapframe *tf) {
    // ...
    // 注意这句话要放在函数的开头，因为后面 tf->cp0_epc 就发生了变化
    u_int bd = tf->cp0_cause >> 31;
    u_int code = *(u_int*) (bd ? tf->cp0_epc + 4 : tf->cp0_epc);
    printf("\nEnv:0x%x, code:0x%x, pgcow:%d, pgout:%d\n", curenv->env_id, code, ++curenv->env_pgcow, curenv->env_pgout);
    // ...
}
```

最后在进程销毁时输出要求的信息：

```c
void env_destroy(struct Env *e) {
    printf("envid:%08x\n", e->env_id);
    printf("pgcow:%08x\n", e->env_pgcow);
    printf("pgout:%08x\n", e->env_pgout);
    // ...
}
```