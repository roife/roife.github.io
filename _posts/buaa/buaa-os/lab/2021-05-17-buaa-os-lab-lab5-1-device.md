---
layout: "post"
title: "「BUAA-OS-Lab」 Lab5-1 外设"
subtitle: "外设与磁盘访问"
author: "roife"
date: 2021-05-17

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "C@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 课上

## Exam

为系统添加外设：时钟与控制台。

### Task 1

#### 题目

实现系统调用 `int syscall_get_time()`，用于调用 gxemul 自带的时钟外设，返回一个 UNIX 时间戳（单位为秒）。

关于 gxemul 自带的时钟外设，文档如下：

```
rtc:
A Real-Time Clock, used to retrieve the current time and to cause periodic interrupts.

Source code:  src/devices/dev_rtc.c

Include file:  dev_rtc.h
Physical address:  0x15000000

Offset:     	Effect:
0x0000	        Read or Write: Trigger a clock update (a gettimeofday() on the host).
0x0010	        Read: Seconds since 1st January 1970
0x0020	        Read: Microseconds
0x0100	        Read: Get the current timer interrupt frequency.
                Write: Set the timer interrupt frequency. (Writing 0 disables the timer.)
0x0110	        Read or Write: Acknowledge one timer interrupt.
                (Note that if multiple interrupts are pending, only one is acknowledged.)
```

#### 分析

注意仔细读文档，会发现这个时钟的工作原理是从宿主机获取时间信息。所以读时间操作分为两步：
- 先对 `0x0000` 进行读写，触发 gxemul 从宿主机获得时间信息并更新自己时间信息
- 从 `0x1000` 读取时间戳

```c
int sys_get_time(int sysno) {
    int addr = 0x15000000 + 0xa0000000;
    int offset = 0x0010;

    int time;
    bcopy(&time, addr+0x00, 4); // Trigger a clock update by writing
    bcopy(addr + offset, &time, 4); // read timestamp
    return time;
}
```

另一个需要注意的是，添加系统调用需要修改这几个文件：

- `/user/lib.h`：添加函数声明
  ```
  int syscall_get_time();
  ```
- `include/unistd.h`：添加系统调用号
  ```c
  #define SYS_get_time           ((__SYSCALL_BASE ) + (17) )
  ```
- `lib/syscall.S`：在尾部添加
  ```c
  .word sys_get_time
  ```
- `user/syscall_lib.c`：实现用户态调用
  ```c
  int syscall_get_time() {
      return msyscall(SYS_get_time, 0, 0, 0, 0, 0);
  }
  ```

### Task 2

#### 题目

实现系统调用 `int syscall_read_str(char *buf, int secno);`，功能是从控制台读取一个以 `\r` 结尾的字符串，并且写入 0 号磁盘的 `secno` 扇区中。

函数需要将读取的字符串存入 `buf`，并且返回字符串的长度。

gxemul 自带的控制台外设使用方法如下：

```
cons:
A simple console device, for writing characters to the controlling terminal and receiving keypresses.

Source code:  src/devices/dev_cons.c

Include file:  dev_cons.h
Physical address:  0x10000000


Offset:     	Effect:
0x00	        Read: getchar()
                    (non-blocking; returns 0 if no char was available)
                Write: putchar(ch)
0x10	        Read or write: halt()
                (Useful for exiting the emulator.)
```

#### 分析

首先和 Task 1 一样修改几个文件添加系统调用。

直接从指定位置 `0x00` 进行读取即可。

```c
int sys_read_str(int sysno, u_int buf2, u_int secno) {
    int addr = 0x10000000 + 0xa0000000;
    int offset = 0x00;

    int len = 0;
    char c = 0;
    char *buf = (char*)buf2;

    while (1) {
        // read from console
        while (c == 0) bcopy(addr + offset, &c, 1);

        if(c == '\r') {
            *buf++ = '\0'; // 注意这里
            break;
        } else {
            *buf++ = c;
            ++len;
        }

        c = 0;
    }

    // write to disk
    int diskno = 0;
    int offset_now = secno * 0x200;
    int write = 1;

    bcopy(&diskno, 0xb3000010, 4);
    bcopy(&offset_now, 0xb3000000, 4);
    bcopy(buf, 0xb3004000, len + 1); // not 0x200
    bcopy(&write, 0xb3000020, 4);

    return len;
}
```

## Extra

之前已经实现了时钟中断，用来实现进程定时切换。现在要添加控制台中断。

Extra 的题目需要在 Exam 的基础上实现。

### Task 1

#### 题目

目前的 MOS 默认只打开了时钟中断。现在要求修改 CP0 寄存器的值，打开控制台的中断。（模仿 `kclock` 的实现，可以参考的文件包括 `lib/genex.S`/`lib/kclock.c`/`lib/kclock_asm.S`/`include/asm/cp0regdef.h`）

gxemul 中 Cause 的各个中断控制位含义如下：

```
IRQ             Used for:
7               MIPS count/compare interrupt
6               mp (inter-processor interrupts)
4               rtc
3               ether
2               cons
```

触发中断时，调用函数 `handle_cons_ir`。

编写完成后需要在 Makefile 中添加对应的编译指令。

#### 分析

这个题目比较复杂，不过好在给出了提示：参考 `klock` 的实现。

下面分成几个部分讲。

#### 中断位初始化（允许中断）

##### `include/asm/cp0regdef.h`

添加对应的中断位，这个位置对应了 CP0 Cause 寄存器中 IPC 的 `cons` 位。（从上面的 `cons` 对应 IPC 的第二位可以得到）

```c
// 已有的
#define STATUSF_IP4 0x1000

// 模仿添加
#define STATUSF_IP2 0x400
```

##### `lib/kcons.c`

这个文件负责创建初始化 CP0 中断位的接口，只需要调用汇编函数 `set_cons()` 即可。

直接模仿 `lib/kclock.c`：

```c
#include <kcons.h>

extern void set_cons();

void kcons_init(void) {
    set_cons();
}
```

##### `lib/kcons_asm.S`

模仿已有的文件，设置对应的中断位为 1，允许中断。

```c
#include <asm/regdef.h>
#include <asm/cp0regdef.h>
#include <asm/asm.h>
#include <kcons.h> // 后面要添加的声明

.macro setup_c0_status set clr
   .set    push
   mfc0    t0, CP0_STATUS
   or  t0, \set|\clr
   xor t0, \clr
   mtc0    t0, CP0_STATUS
   .set    pop
.endm

.text
LEAF(set_cons)
    li t0, 0x0
    sb t0, 0xb5000100 // 屏蔽掉计时器的中断，防止干扰
    sw  sp, KERNEL_SP
setup_c0_status STATUS_CU0|STATUSF_IP2|0x1 0
    jr ra

    nop
END(set_cons)
```

`setup_c0_status` 这个宏不难发现是用来设置 CP0 状态寄存器的值的。

#### 中断处理

##### `lib/genex.S`

首先在 `NESTED(handle_int, TF_SIZE, sp)` 下面模仿时钟中断 `timer_irq` 添加控制台中断：

```mips
// 已有的
andi    t1, t0, STATUSF_IP4
bnez    t1, timer_irq
nop

// 模仿上面的
andi    t1, t0, STATUSF_IP2 // 前面在 cp0regdef.h 添加的，用于识别中断位
bnez   t1, cons_irq         // 发生中断，跳到对应的处理代码段
nop
```

然后在下面添加中断处理代码 `cons_irq`：

```mips
// 已有的
timer_irq:
1:  j   sched_yield
    nop
    /*li t1, 0xff
    lw    t0, delay
    addu  t0, 1
    sw  t0, delay
    beq t0,t1,1f
    nop*/
    j   ret_from_exception
    nop

// 模仿上面的
cons_irq:
   jal     handle_cons_ir       # 发生中断时跳转到处理函数
   nop
   j       ret_from_exception
   nop
```

#### 函数声明/编译链接

##### `include/kcons.h`

添加对应的声明，模仿 `kclock.h`：

```c
#ifndef _KCONS_H_
#define _KCONS_H_
#ifndef __ASSEMBLER__

void kcons_init(void);
void handle_cons_ir(char c, int status);

#endif /* !__ASSEMBLER__ */
#endif
```

##### `lib/Makefile`

将编译的 `.o` 文件添加到链接命令中：

```makefile
all: ... kcons.o kcons_asm.o handle_cons_ir.o
```

### Task 2

#### 题目

实现 `handle_cons_ir` 函数，它需要完成以下几件事：
- 在**第一次**触发控制台中断时打印
  ```c
  printf("CP0 STATUS: %x, 1st interrupt: %d\n", status, time);
  ```
  `status` 是进入中断处理程序时 CP0 `STATUS` 寄存器的值，`time` 是第一次触发控制台中断时的 UNIX 标准时间（单位为秒）
- 在之后触发控制台中断时需要打印
  ```c
  printf("interval: %d\n", interval);
  ```
  `interval` 表示**当前时间**和**第一次**触发控制台中断的时间差，单位为秒。
- 当 `interval` 的值大于等于 5 时需要**结束** gxemul 的模拟。在结束模拟前需要打印
  ```c
  printf("length=%d, string=%s\n", length, string);
  ```
  `string` 是将所有控制台输入的字符进行拼接的结果（只有字母和数字），`length` 字符串长度（不超过 128）。

#### 分析

注意多次调用函数，每次的状态可以用静态变量记录。

这里调用了 Exam 里面实现的 `sys_get_time` 函数，所以需要声明。

当 `interval > 5` 时需要终止程序。观察 Exam Task 2 给的文档，发现只要向控制台的 `0x10` 位置读/写就可以终止控制台。

```c
extern int sys_get_time(int sysno);

void handle_cons_ir(int status) {
    static int kase = 0;
    static int time = 0;
    static char buf[512];
    static int len = 0;

    int addr = 0x10000000 + 0xa0000000;
    char c;
    bcopy(addr + 0x00, &c, 1); // read from console

    int interval = sys_get_time(1) - time;
    if (kase++ == 0) {
        time = sys_get_time(1);
        buf[len++] = c;
        printf("CP0 STATUS: %x, 1st interrupt: %d\n", status, time);
    } else {
        printf("interval: %d\n", interval);
        buf[len++] = c;
        if (interval >= 5) {
            buf[len++] = '\0';
            printf("length=%d, string=%s\n", len - 1, buf);
            bcopy(addr + 0x10, &c, 1); // halt
        }
    }
}
```

注意到这里传入了参数 `status` 表示 CP0 `CAUSE` 寄存器的值，所以需要在调用处将其作为参数传入。这里修改 `lib/genex.S`：

```c
cons_irq:
   mfc0     a0, CP0_STATUS // status
   jal      handle_cons_ir
   nop
   j        ret_from_exception
   nop
```