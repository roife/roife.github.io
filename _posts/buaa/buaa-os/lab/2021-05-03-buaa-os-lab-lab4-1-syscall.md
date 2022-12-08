---
layout: "post"
title: "「BUAA-OS-Lab」 Lab4-1 系统调用"
subtitle: "系统调用 & 进程通信"
author: "roife"
date: 2021-05-03

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "C@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

> 好难啊
>
> 感谢 @DDoSolitary 开源的实验代码提供的帮助

# 课上

## Exam

原始的 MOS 系统中系统调用的参数数量是确定的，但是现实中系统调用的参数数量并不是固定的，下面需要实现参数数量不固定的系统调用。

### Task 1

#### 题目

修改规则如下：
- 第一个参数为系统调用号
- 第二个参数为此系统调用参数个数
- 后面的参数是系统调用真正的参数（数量与第二个参数一致）

例如：

```c
int syscall_mem_map(u_int srcid, u_int srcva, u_int dstid, u_int dstva, u_int perm) {
    return msyscall(SYS_mem_map, 5, srcid, srcva, dstid, dstva, perm);
}
```

修改完成后需要用这个规则改写所有已有的系统调用。

提示：内核态处理系统调用参数，合理操作寄存器与栈，以保证在原有 `lib/syscall_all.c` 中代码不更改的情况下可以使系统调用机制正常运行。

#### 分析

##### 修改用户态系统调用声明

由于系统调用的参数不固定了，因此需要修改 `user/lib.h` 中的系统调用声明：

```c
extern int msyscall(int, int, ...);
```

##### MIPS 函数调用约定

我们要处理的是系统调用参数的转发

首先回忆一下 MIPS 中函数调用的约定（ABI）。

1. 全局寄存器由调用的函数保存（由于是我们调用编译器编译的系统调用，所以都是编译器保存），临时寄存器由调用者保存（我们保存）
2. 函数参数优先存在 `$a0 ~ $a3`，存不下就只能放在内存
3. 函数调用时用了 `n` 个参数，就要在栈里留出 `n` 个位置用来存参数。如下图所示
   - 其中 `sp+0 ~ sp+3` 个位置对应的参数已经在寄存器里面了，所以不用管；
   - `sp+3 ~` 的位置用来存寄存器里放不下的参数

```c
f(a0, a1, a2, a3, a4, a5, ...)
```

![MIPS call ABI](/img/in-post/post-buaa-os/mips-call-abi.png){:height="450px" width="450px"}

##### 分析 `lib/syscall.S`

```mips
// 已经将 trapframe（由陷入内核态前的 32 个寄存器的值组成）存在栈上
lw      a0, TF_REG4(sp)             // trapframe 中编号为 4 的寄存器恰好对应着陷入内核态前的 a0，即系统调用号

addiu   a0, a0, -__SYSCALL_BASE     // a0 <- 第几个系统调用
sll     t0, a0, 2                   // t0 <- 乘以 4 转换成 sys_call_table 中的偏移
la      t1, sys_call_table          // t1 <- 加载 sys_call_table 数组
addu    t1, t1, t0                  // t1 <- 找到系统调用在数组中的地址
lw      t2, 0(t1)                   // t2 <- 得到真正系统调用函数地址，即 sys_*（由编译器算好存在 sys_call_table）

lw      t0, TF_REG29(sp)            // t0 <- 原先用户的栈指针
lw      t3, 16(t0)                  // t3 <- msyscall 的第五个参数
lw      t4, 20(t0)                  // t4 <- msyscall 的第六个参数

// 从 trapframe 中读取陷入内核前 4 个参数传递寄存器，转移到当前的寄存器中，当作调用参数
lw      a0, TF_REG4(sp)
lw      a1, TF_REG5(sp)
lw      a2, TF_REG6(sp)
lw      a3, TF_REG7(sp)

// 调用函数前栈指针向下移动，用于存储参数
addiu   sp, sp, -24

// 寄存器存满了，只能将第五个、第六个参数存入栈
sw      t3, 16(sp)
sw      t4, 20(sp)

jalr    t2                          // 跳到 sys_*
nop

// 恢复之前的栈指针偏移
addiu   sp, sp, 24

sw      v0, TF_REG2(sp)             // 将 sys_* 的返回值转移到 trapframe 中，用户态会将其当作调用返回值
```

##### 修改 `lib/syscall.S`

```mips
// 同上，t2 <- sys_* 的地址
addiu   a0, a0, -__SYSCALL_BASE
sll     t0, a0, 2
la      t1, sys_call_table
addu    t1, t1, t0
lw      t2, 0(t1)

lw      t0, TF_REG29(sp)            // t0 <- 原先用户的栈指针
move    s0, sp                      // 将现在的栈指针保存在全局变量，编译器负责保护，不保护会丢失

// 用一个循环将应该保存在内存中的参数转移过来
LOOP_BEGIN:
    // a1 是第二个参数，即系统调用参数数量
    // 若参数小于 3 则可以全部保存在寄存器中，不再折腾内存
    ble     a1, 3, LOOP_END
    nop

    // 参数要向前挪一个位置
    addiu   t1, a1, 1
    sll     t1, t1, 2               // t1 <- 参数在旧栈空间中的偏移
    addu    t1, t1, t0              // t1 <- 参数在旧栈空间中的位置
    lw      t1, 0(t1)               // t1 <- 从旧栈空间中读取参数

    // 存到栈里
    addiu   sp, sp, -4
    sw      t1, 0(sp)

    addiu   a1, a1, -1
    b       LOOP_BEGIN
    nop
LOOP_END:

// 将应该保存在寄存器中的参数转移过来，即向前挪一个位置
// 注意 a3 要从旧栈空间的内存中读取了
addiu   sp, sp, -16
move    t1, a1
move    a1, a2
move    a2, a3

bne     t1, 3, SKIP_A3
nop

lw      a3, 16(t0)

SKIP_A3:

jalr    t2                          // Invoke sys_* function
nop

move sp, s0                         // 从全局寄存器恢复原来的栈指针

sw      v0, TF_REG2(sp)
```

##### 修改已有系统调用

做完这些后，按照题目给的例子在 `user/syscall_lib.c` 中改写所有的已有的系统调用即可，这一步不再赘述（不要漏了 `user/lib.h` 中的 `syscall_env_alloc`）。

### Task 2

#### 题目

实现系统调用 `syscall_ipc_can_multi_send` 支持同时向 5 个进程通信，其函数声明为：

```c
int syscall_ipc_can_multi_send(u_int value, u_int srcva, u_int perm, u_int envid_1, u_int envid_2, u_int envid_3, u_int envid_4, u_int envid_5);
```

其中参数的含义与 `syscall_ipc_can_send` 相同。

约束如下：
- 若接收的进程 `env_ipc_recving` 不全为 `1`，则返回 `-E_IPC_NOT_RECV`；否则发送消息
- 系统调用必须为原子操作，即不可使用 `ipc_send`函数来完成操作，必须要实现 `sys_ipc_can_multi_send`
- 发送成功时返回 `0`

#### 分析

只要 Task 1 实现正确，那么 Task 2 实现起来非常简单：

1. 首先在 `include/unistd.h` 中添加系统调用号
   ```c
   #define SYS_ipc_can_multi_send ((__SYSCALL_BASE) + (15))
   ```

2. 在 `lib/syscall.S` 中添加相应字段
   ```c
   .word sys_ipc_can_multi_send
   ```

3. 在 `lib/syscall_all.c` 中实现系统调用
    ```c
    int sys_ipc_can_multi_send(int sysno, u_int value, u_int srcva, u_int perm,
        u_int envid_1, u_int envid_2, u_int envid_3, u_int envid_4, u_int envid_5) {

        int r;
        struct Env *e[5];
        struct Page *p;

        if (srcva >= UTOP) return -E_INVAL;
        if ((r = envid2env(envid_1, e, 0)) < 0) return r;
        if ((r = envid2env(envid_2, e+1, 0)) < 0) return r;
        if ((r = envid2env(envid_3, e+2, 0)) < 0) return r;
        if ((r = envid2env(envid_4, e+3, 0)) < 0) return r;
        if ((r = envid2env(envid_5, e+4, 0)) < 0) return r;

        int i;
        for (i = 0; i < 5; i++) {
            if (!e[i]->env_ipc_recving) return -E_IPC_NOT_RECV;
        }

        for (i = 0; i < 5; i++) {
            if (srcva) {
                p = page_lookup(curenv->env_pgdir, srcva, NULL);
                page_insert(e[i]->env_pgdir, p, e[i]->env_ipc_dstva, perm);
            }
            e[i]->env_ipc_value = value;
            e[i]->env_ipc_from = curenv->env_id;
            e[i]->env_ipc_perm = perm;
            e[i]->env_ipc_recving = 0;
            sys_set_env_status(0, e[i]->env_id, ENV_RUNNABLE);
        }
        return 0;
    }
    ```
4. 在 `user/lib.h` 中添加用户态的说明并在 `user/syscall_lib.c` 进行调用
    ```c
    // user/lib.h
    int syscall_ipc_can_multi_send(u_int value, u_int srcva, u_int perm,
        u_int envid_1, u_int envid_2, u_int envid_3, u_int envid_4, u_int envid_5);
    ```

    ```c
    // user/syscall_lib.c
    int syscall_ipc_can_multi_send(u_int value, u_int srcva, u_int perm,
        u_int envid_1, u_int envid_2, u_int envid_3, u_int envid_4, u_int envid_5) {

        return msyscall(SYS_ipc_can_multi_send, 8, value, srcva, perm,
                            envid_1, envid_2, envid_3, envid_4, envid_5);
    }
    ```

## Extra

实现进程通信中的转发机制，即 `A` 为了发消息给 `C`，先发消息到 `B`，`B` 再转发到 `C`。

### 题目

在 `env` 控制块中增加一个叫做 `env_ipc_destination_id` 的成员表示最终目标进程 id。

然后修改 `ipc_send` 函数，加入 `transfer_id` 参数，表示中转进程。声明如下：

```c
void ipc_send(u_int whom, u_int value, u_int transfer_id, u_int srcva, u_int perm);
```

- 若 `transfer_id` 为 `-1`，则代表不需要转发，直接与目标进程进行通信
- 否则保证 `transfer_id` 一定是一个存在的进程 id，发送进程只需与转发进程直接通信即可（相当于只是修改一下目标进程）

### 分析

首先按照题目说的在 `include/env.h` 中添加对应的字段：

```c
// include/env.h
struct Env {
    u_int env_ipc_destination_id;
    // ...
}
```

在 `user/lib.h`/`user/ipc.c`/`user/syscall_lib.c` 修改 `ipc_send` 和 `syscall_ipc_can_send` 系统调用的函数签名：


```c
// user/lib.h
int syscall_ipc_can_send(u_int envid, u_int value, int transfer_id, u_int srcva, u_int perm);
void ipc_send(u_int whom, u_int val, int transfer_id, u_int srcva, u_int perm);
```

```c
// user/ipc.c
void ipc_send(u_int whom, u_int val, int transfer_id, u_int srcva, u_int perm) {
    int r;

    while ((r = syscall_ipc_can_send(whom, val, transfer_id, srcva, perm)) == -E_IPC_NOT_RECV) {
         syscall_yield();
     }
}
```

```c
// user/syscall_lib.c
int syscall_ipc_can_send(u_int envid, u_int value, int transfer_id, u_int srcva, u_int perm) {
    return msyscall(SYS_ipc_can_send, envid, value, transfer_id, srcva, perm);
}
```

不要忘记在使用处也要修改（用 `grep` 找一下）：

```c
// user/fsipc.c
ipc_send(envs[1].env_id, type, -1, (u_int)fsreq, PTE_V | PTE_R);
```

最后考虑修改在 `lib/syscall_all.c` 中修改系统调用 `sys_ipc_can_send`：

```c
int sys_ipc_can_send(int sysno, u_int envid, u_int value, int transfer_id, u_int srcva, u_int perm) {
    int r;
    struct Env *e;
    struct Page *p;

    if (srcva >= UTOP) return -E_INVAL;
    // 如果 transfer_id 为 -1 说明直接转发即可，此时 transfer_id 存的是目标 id
    if (transfer_id == -1) transfer_id = envid;
    if ((r = envid2env(transfer_id, &e, 0)) < 0) return r;
    if (!e->env_ipc_recving) return -E_IPC_NOT_RECV;

    if (srcva) {
        if (!(p = page_lookup(curenv->env_pgdir, srcva, NULL))) {
            return -E_INVAL;
        }
        if ((r = page_insert(e->env_pgdir, p, e->env_ipc_dstva, perm)) < 0) {
            return r;
        }
    }

    e->env_ipc_value = value;
    e->env_ipc_from = curenv->env_id;
    e->env_ipc_perm = perm;
    e->env_ipc_recving = 0;
    e->env_ipc_destination_id = envid; // 设置 env_ipc_destination_id 的值

    // 切换到 transfer_id
    if ((r = sys_set_env_status(0, transfer_id, ENV_RUNNABLE)) < 0) return r;

    return 0;
}
```