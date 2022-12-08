---
layout: "post"
title: "「BUAA-OS-Lab」 Lab1-2 内核制作、启动和 printf"
subtitle: "printf 函数 & 系统启动"
author: "roife"
date: 2021-03-30

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "MIPS@编程语言", "C@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 课上

做 Lab1-2 的时候一定要学会调试 `printf`！

方法是在 `init/main.c` 里面添加 `printf` 语句，这里的 `printf` 就是自己写的函数。

## Exam

### 题目

修改 `printf` 函数，使其支持输出结构体。结构体格式总共有两种：

```c
struct s1 {
    int a;
    char b;
    char c;
    int d;
}

struct s2 {
    int sizec;
    int c[sizec]; // 即保证 c 数组长度为 sizec
}
```

对于 `s1`，输出格式为 `{1,b,c,4}`；对于 `s2`，输出格式为 `{2,2,3}`，注意第一个输出的数字是 `sizec`。

### 分析

主要是传入结构体参数怎么访问到其中的元素。我们可以在 `print.c` 里面按照定义一个结构体，然后用箭头运算符去访问。

也可以直接访问地址，如 `*(addr + 4)`，但是要注意结构体内数据的排列要字对齐（尤其是 `char`）。

另一个需要注意的是，如果定义结构体，那么这个数组的长度不能写 `c[size]`，因为这里 `size` 是不知道的。可以随便填一个数字或者不写，如 `c[100]` 或 `c[]`。而且这里的数组也不能用 `int *c`，因为此时 `c` 里面并非数组的地址，而是数组第一个元素的值。

输出就模仿原来的代码即可，这里我用宏简化了代码。

```c
struct s1 {
    int a;
    char b;
    char c;
    int d;
};

struct s2 {
    int size;
    int c[]; // 注意这里不能写 int c[size]
    // 也可以写 int c[1] 等
};

void
lp_Print(void (*output)(void *, char *, int),
         void * arg,
         char *fmt,
         va_list ap)
{
    // ...

    int stypeid;

    // ...

    for (;;) {
        // ...

        /* check for struct*/
        stypeid = 0;
        if (*fmt == '$') {
            ++fmt;
            stypeid = Ctod(*fmt++);
        }

        switch(*fmt) {
            // ...
            case 'T':
                // 注意输出 {}，时，width 为 0
                #define PrintC(c) \
                    { \
                        length = PrintChar(buf, '{', 0, ladjust); \
                        OUTPUT(arg, buf, length); \
                    }
                #define PrintInt(x) \
                    { \
                        num = x; \
                        if (num < 0) num = -num, negFlag = 1; \
                        length = PrintNum(buf, num, 10, negFlag, width, ladjust, padc, 0); \
                        OUTPUT(arg, buf, length); \
                        negFlag = 0; \
                    }

                PrintC('{');
                if (stypeid == 1) {
                    struct s1* addr = (struct s1*)va_arg(ap, int);

                    PrintInt(addr->a);
                    PrintC(',');

                    PrintC(addr->b);
                    PrintC(',');

                    PrintC(addr->c);
                    PrintC(',');

                    PrintInt(addr->d);
                } else if (stypeid == 2) {
                    struct s2* addr = (struct s2*)va_arg(ap, int);
                    long int size = addr->size;

                    // print size
                    PrintInt(addr->size);
                    PrintC(',');

                    // print array
                    for (i=0; i<size; ++i) {
                        PrintInt(addr->c[i]);
                        if (i != size - 1) {
                            PrintC(',');
                        }
                    }
                }
                PrintC('}');
                break;
            // other cases
        }
    }
}
```

## Extra

新建一个 `my_cal` 文件夹，并且创建三个文件：`Makefile`、`my_cal.c`、`my_driver.S`。

### Task 1

#### 题目

编写 `Makefile` 编译 `my_cal.c` 和 `my_driver.S`。

#### 分析

这个模仿 `boot` 和 `init` 下面的 `Makefile` 就好了，注意 `.S` 和 `.o` 都要编译。

```makefile
INCLUDES        := -I../include

%.o: %.c
        $(CC) $(DEFS) $(CFLAGS) $(INCLUDES) -c $<
%.o: %.S
        $(CC) $(CFLAGS) $(INCLUDES) -c $<

.PHONY: clean

all: my_driver.o my_cal.o

clean:
        rm -rf *~ *.o


include ../include.mk
```

### Task 2

#### 题目

编写 `my_driver.S` 实现三个函数：
- `char _my_getchar()`：从控制台读入字符
- `void _my_putchar(char)`：输出字符
- `void _my_exit()`：退出模拟器

有几点注意事项：
- `_my_getchar()` 读入一个字符时，要立即输出，这样才能在控制台上回显
- 如果 `_my_getchar()` 读入了 `\r`，那么要补充输出一个 `\n`
- 使用 `_my_getchar()` 的时候控制台可能没有输入（即读到的内容为 `0`），此时应该有一个循环不断访问，直到要字符为止
- 设备的物理地址为 `0x10000000`，`0x00` 是读写控制台的地址，`0x10` 是终止程序的地址。向 `0x00` 写入数据可以在控制台显示数据，从 `0x00` 读入数据可以从控制台读入数据
- 汇编函数的写法可以参考 `boot/start.S`

#### 分析

首先的问题是怎么用汇编写函数，观察 `boot/start.S` 发现其结构是这样的：

```mips
LEAF(NAME)
    /* ASM */
END(NAME)
```

所以仿照这个写就行了。读取传入参数、返回值、结束函数和普通的 MIPS 函数一样，访问 `$a0`/`$v0`/`$ra` 即可。

因为这里引用了一个头文件，里面提供了寄存器的简写方式。所以写寄存器的时候可以直接用 `a0`/`v0`/`ra`。

然后的问题就是要读写哪个地址。由于我们访问的是外设，所以不能经过 cache，观察 MIPS 的内存布局可以发现应该是 `kseg1`，起始地址为 `0xA0000000`，再加上物理地址 `0x10000000`，即应该要访问的内存为 `0xB0000000` 与 `0xB0000010`。

其实从 `drivers/gxconsole` 下面的 `console.c` 和 `dev_cons.h` 文件也不难发现读写外设访问的是 `0xB0000000` 这个地址，终止程序的是 `0xB0000010`。

```c
#include <asm/regdef.h>
#include <asm/cp0regdef.h>
#include <asm/asm.h>

LEAF(_my_getchar)
    li t0, 0xB0000000
    loop:
        lb t1, 0(t0) /* read a char to $t1 */
        beq t1, zero, loop
        nop
    end_loop:
    sb t1, 0(t0)

    /* check \r */
    li t2, 13 /* \r */
    bne t1, t2, end_check_r
    nop
    check_r:
        li t2, 10 /* \n */
        sb t2, 0(t0)
    end_check_r:

    or v0, zero, t1
    jr ra /* 注意函数调用要返回！ */
END(_my_getchar)

LEAF(_my_putchar)
    li t0, 0xB0000000
    sb a0, 0(t0)
    jr ra
END(_my_putchar)

LEAF(_my_exit)
    li t0, 0xB0000000
    sb zero, 0x10(t0)
    jr ra
END(_my_exit)
```

### Task 3

#### 题目

利用 `char _my_getchar()` 和 `void _my_putchar(char)` 写一个计算加法的程序，即读入两个正整数，用 `\n` 分隔，将其相加然后输出。

保证数字在 `int` 范围内，不能使用 `printf`。

#### 分析

就是一个快读快写。

为了让程序能访问到我们自己编写的函数，需要在程序头部对用到的函数进行声明。

数字在 `int` 范围内，输出的时候注意一下。

自己测试的时候，换行不能直接敲回车，要使用 `Ctrl + j`，这样才是 `\n`。

```c
// 课上写的很丑的代码
char _my_getchar();
void _my_putchar(char ch);

void my_cal() {
    char c = _my_getchar();
    int a = 0;
    int b = 0;
    while (c != '\n') {
        a = a * 10 + c - '0';
        c = _my_getchar();
    }
    c = _my_getchar();
    while (c != '\n') {
        b = b * 10 + c - '0';
        c = _my_getchar();
    }
    int d = a + b;
    if (d == 0) _my_putchar('0');
    else {
        int e = 1000000000;
        while (d / e == 0) e = e / 10;
        while (e) {
            _my_putchar(d / e + '0');
            d = d % e;
            e = e / 10;
        }
    }
}
```

```c
// 快读快写版本
char _my_getchar();
void _my_putchar(char ch);
inline int isdigit(char c) { return c>='0' && c<='9'; }

int rd() {
    int x = 0; char c;
    while(!isdigit(c = _my_getchar())); x = c^48;
    while(isdigit(c = _my_getchar())) x=(x<<1)+(x<<3)+(c^48);
    return x;
}

void wr(int x) {
    static char c[10], *s=c; *s=0;
    do *++s=x%10^48; while(x/=10);
    while(*s) _my_putchar(*s--);
}

void my_cal() {
    wr(rd() + rd());
}
```