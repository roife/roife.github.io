---
layout: "post"
title: "「BUAA-CO」 08 异常及高级微体系架构介绍"
subtitle: "异常，分支预测以及高级处理器"
author: "roife"
date: 2021-01-17
tags: ["北航计算机组成理论@课程相关", "课程相关@Tags", "Digital Design and Computer Architecture@读书笔记", "读书笔记@Tags", "体系结构@Tags", "集成电路@Tags", "CPU@体系结构"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 异常

异常是 CPU 发生错误时采取的错误处理手段。注意，这里说的异常是硬件异常，和软件异常不一样。发生异常时，处理器会保存发生异常的 PC 到 EPC 和异常原因等信息，然后跳到 Handler 去处理异常。所以异常可以看成一个特殊的跳转指令。

一般异常由 CPU 之外的另一个处理器 CP0 协处理器处理。CP0 中有 32 个寄存器，定义了一些处理异常和中断的功能。其中 13 好处理器 `Cause` 表示异常的原因，14 号处理器 `EPC` 表示异常发生的位置。用 `mfc0` 可以从协处理器中读取出对应寄存器的值。

![processor-exceptions](/img/in-post/post-buaa-co/processor-exceptions.png)

修改后的数据路径支持接收异常信号传给 CP0，并且支持从 CP0 中用 `mfc0` 读取相应的寄存器。

![processor-exceptions-control](/img/in-post/post-buaa-co/processor-exceptions-control.png)

新的控制器在接收到非法指令后会跳到 `S12` 保存现场（`EPC` 和 `Cause`）然后跳到异常处理，如果接收到溢出信号跳到 `S13`然后跳到异常处理。如果接收到 `mfc0` 指令则会跳到 `S14` 并读取对应的寄存器。

# CP0

CP0 是 MIPS CPU 中处理中断和异常的一个协处理器。可以用 `mfc0` 和 `mtc0` 对其进行读写，使用 `eret` 从异常处理程序返回到 `EPC` 中。

CP0 中定义了 32 个寄存器用来保存 CPU 的状态，常用的有以下 4 个：
- `SR`：用于对系统进行控制
  + `IE[1]`：是否允许中断
  + `EXL[1]`：是否处于中断中
  + `IM[15:10]`：是否允许对应的中断源进行中断
- `Cause`：指令读取，硬件控制写入
  + `BD[31]`：发生中断异常的是否为延迟槽指令
  + `IP[15:10]`：对应外部 6 个中断源
  + `ExcCode[6:2]`：异常/中断类型编码值（即异常/中断的类型）
- `EPC`：用于保存异常/中断发生时的 PC
- `PRId`：处理器 ID，可以用于实现个性的编码

# 高级微体系架构

## 深流水线

继续分割流水线使得每个阶段包含尽量少的逻辑（越 10～20 级），因此可以运行得更快。但是流水线变长往往会产生更多阻塞，而且会产生时序上的开销，所以不一定阶段越多速度越快。

## 分支预测

分支预测指在分支跳转时猜测跳转的位置，以此减少指令被清除的可能性。

分支预测分为静态分支预测（static branch prediction）与动态分支预测（dynamic branch prediction）。前者比如对于循环等分支应该预测跳转，因为循环一般会执行多次。通常用的是后者。

动态分支预测会使用动态分支预测器（dynamic branch predictor），其保存了最近执行的几百几千条指令，被称为分支目标缓冲器（branch target buffer），记录了分支的目标地址和此分支是否发生过的历史。

对于一位动态分支预测器（one-bit dynamic branch predictor）而言，会记录当前分支上一次是否跳转，并且预测这次的情况和上次相同。

对于两位动态分支预测器，采用了一个两位的状态机：强跳转（strongly taken），弱跳转（weakly taken），弱不跳转（weakly not taken），强不跳转（strongly not taken）。

![2-bit-dynamic-branch-predictor](/img/in-post/post-buaa-co/2-bit-branch-predictor.png)

Predicator 一般在流水线的取指阶段运行。

## 超标量处理器

超标量处理器指数据路径增加使得同时可以执行多个指令，如在数据路径中放置两个 ALU 等。

![superscalar](/img/in-post/post-buaa-co/superscalar.png)

## 乱序处理器

乱序处理器可以打乱指令之间的顺序，使得没有寄存器相关的程序一起执行，在保证执行结果不变的情况下尽可能不暂停。

寄存器相关分为三种：
- 读后写（RAW）：即前一个指令写入的寄存器，后面一个指令要用到，如 `lw $t0, 0($t1) / add $s0, $t0, $s1`
- 写后读（WAR）：即后一个指令写入的寄存器，前面一个指令要用到。如 `add $s0, $t0, $s1 / sub $t0, $t2, $t3`。这导致 `sub` 不能在 `add` 之前执行，这种冲突只会在乱序处理器中遇到。这种相关性可以消除。
- 写后写（WAW）：即前一个指令写入的寄存器，和后一个指令写入的寄存器相同。如 `add $s0, $t0, $s1 / sub $s0, $t2, $t3`，类似于 WAR，此时前一条指令写入的值应当被丢弃。类似于 WAR，这也是可以避免的，直接丢弃前面一条 `add` 即可。

### 寄存器重命名

寄存器重命名（register renaming）是一种避免 WAR 的技术。寄存器重命名技术通过增加一些内部的寄存器，用起作为中转站来减少 WAR 的冲突。

如增加 20 个重命名寄存器 $r0 ~ r19$。对于 WAR 的指令序列可以将后者写入的寄存器命名为 $r0$，这样就避免了后前一条指令冲突。（注意，此时后面的指令序列如果用到了这个寄存器，那么也要重命名为 $r0$）

```mips
add $s0, $t0, $s1
sub $t0, $t2, $t3 ; 变成 sub $r0, $t2, $t3
and $s1, $t0, $s2 ; 变成 and $s1, $r0, $s2
```

## 单指令流多数据

即 SIMD（Single Instruction Multiple Data），用一条指令对多个数据进行操作。

比如想要对四组两个 8 位数进行对应的加法运算，可以将其看作两个 32 位数然后运算。

## 多线程

多线程也是多套体系架构，可以同时运行指令。超标量和它的区别在于超标量是多套体系架构运行的一个线程，而多线程运行的是多个线程。

多线程仅仅增加了 PC 和寄存器文件的数量。

## 同构多处理器

同构多处理技术（homogeneous multiprocessing）又称为对称多处理技术（Symmetric MultiProcessing，SMP）即多核处理器技术。一个处理器上集成多个核心。

## 异构多处理器

由于程序不能充分利用所有的核心，所以添加通用核心不一定能提高性能，此时可以使用异构多处理器。

异构多处理器有两种。一种是多个核心使用相同的 ISA，但是处理器设计不同，比如大小核设计使得处理器更加节能。另一种是专用计算处理器，比如浮点协处理器加速浮点运算。