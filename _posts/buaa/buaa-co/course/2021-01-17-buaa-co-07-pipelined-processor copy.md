---
layout: "post"
title: "「BUAA-CO」 07 流水线处理器"
subtitle: "流水线处理器及冲突解决"
author: "roife"
date: 2021-01-17
tags: ["BUAA - 计算机组成@Courses@Series", "Digital Design and Computer Architecture@Books@Series", "北航@Tags@Tags", "计算机组成@Tags@Tags", "数字电路@Tags@Tags", "Verilog-HDL@Languages@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 流水线处理器

流水线的做法类似于多周期。多周期中每个周期只有一条指令在执行，而流水线中同一时间不同阶段有不同的指令一起执行。
为了防止不同阶段的数据互相干扰，需要在数据路径中插入流水线寄存器来隔离组合电路。

但是由于不同的指令之间可能会发生冲突的问题，因此需要一个专门的冲突单元来解决冲突，手段包括转发、阻塞等。

# 流水线数据路径

流水线数据路径和单周期大同小异，相当于直接在其中插入流水线寄存器即可。需要注意的一点就是在流水线中，所有信息（比如 ALU 结果，控制信号等）都要跟着指令一起流水。

![pipelined-processor-with-control](/img/in-post/post-buaa-co/pipelined-processor-with-control.png)

为了方便，把每个周期的寄存器按照所在阶段分别命名为 `DEMW` 级寄存器。

# 冲突

## 什么是冲突

冲突（Hazards）也称为冒险。
多条指令同时执行时，可能会发生一条指令需要某个数据，而更新这个数据的指令还在流水线中，也就是当前指令拿到的数据是老的数据，新的数据还没传过来，这就被称为冲突。例如下面的指令序列：

```mips
add $s0, $s2, $s3
and $t0, $s0, $s1 ; 要用到 add 的 $s0
or  $t1, $s4, $s0 ; 要用到 add 的 $s0
sub $t2, $s0, $s5 ; 要用到 add 的 $s0
```

## 转发

转发（Forwarding）也称为旁路（bypassing）可以解决一类特殊的冒险。它指的是如果当前指令需要的数据已经算出来了，只是没有写到 GRF 里面，那么可以直接从后面的阶段将新的数据传递过来，代替老的数据。

例如这个指令序列：

```mips
add $s0, $s2, $s3
and $t0, $s0, $s1 ; 可以通过转发解决冲突
or  $t1, $s4, $s0 ; 可以通过转发解决冲突
sub $t2, $s0, $s5 ; 可以通过转发解决冲突
```

![forwarding-diagram](/img/in-post/post-buaa-co/forwarding-diagram.png)

在数据路径添加转发路径实际上就是用 MUX 选择，如果满足转发的条件，那么就优先使用转发的数据。如果有多个转发的数据，那么优先使用更新的数据（如 D 级比 E 级优先）。

![forwarding-datapath](/img/in-post/post-buaa-co/forwarding-datapath.png)

## 阻塞

阻塞（stall）可以解决另一类特殊的冒险。虽然转发能解决已经算出结果的寄存器数据，但是还有一种情况下是当前的指令需要用到新数据，但是新数据还没有产生，此时不得不暂停后面指令的执行。等待数据产生完毕才能继续。

例如这个指令序列：

```mips
lw  $s0, 40($0)
and $t0, $s0, $s1 ; 需要阻塞
or  $t1, $s4, $s0
sub $t2, $s0, $s5
```

![stall-diagram](/img/in-post/post-buaa-co/stall-diagram.png)

阻塞的做法就是清空被阻塞阶段下一阶段的流水线，同时取消前面流水线寄存器的写使能以及 PC 的写使能。

比如 D 级的这一指令需要被阻塞，则：
- 清空 E 级寄存器的数据（相当于插入一个 nop 指令，叫做气泡）
- 取消 D 级的写使能（防止前面的指令进来）
- 取消 PC 的写使能（防止进来新的指令）

![stall-datapath](/img/in-post/post-buaa-co/stall-datapath.png)

## 跳转指令

跳转指令会带来另一个冲突的问题：我们在 D 级判断是否会跳转，此时 F 级是 PC+4 的指令，如果跳转了，理论上我们要执行的下一条指令是跳转目标，但是由于流水线寄存器的原理，进入了 D 级的是 PC+4 这条指令。

这个时候我们考虑延迟槽（Delay Slot）技术。在 MIPS 处理器中，我们默认跳转指令的下一跳指令一定执行。例如指令 `ABCD`中，`A` 是跳转指令，要跳到 `D`，我们默认不管跳不跳都要执行 `B`，也就是说执行的指令为 `ABD` 或 `ABCD`。

那么这条 `B` 指令不是很反直觉吗，我们是否特殊处理？作为 CPU 设计者，我们不需要考虑这个事情，这个事情由生成汇编代码的编译器或者指令编写者考虑，延迟槽技术是一个 CPU 设计者与 MIPS 指令编写者的一个约定，如果他们不知道要写啥，可以直接写一个 nop 来充当延迟槽。有了延迟槽技术以后，就可以不需要考虑跳转指令带来的冲突问题了，所以这是十分自然的一个技术。

为了方便起见，我们规定延迟槽中的指令不能是跳转指令。

当然，延迟槽技术也只是一个妥协，现在一般使用分支预测来解决跳转指令的问题。

![pipelined-processor-full-hardzards](/img/in-post/post-buaa-co/pipelined-processor-full-hardzards.png)

（注意，*Digital Design and Computer Architecture* 这本书不使用延迟槽技术，因此如果发生了跳转就要改变 PC 传入流水线寄存器的值）

# 课上

为了方便起见，只要考虑 CPU 的都冲突在 D 级识别和处理。

## 数据路径

和书上的大同小异。

![pipelined-processor-datapath](/img/in-post/post-buaa-co/pipelined-processor-datapath.png)

## 可能发生的冲突

- 结构冲突：IM 和 DM 实际上是一个部件，取指令的时候就不能读取数据了。一般会将指令部分和数据部分分成两个结构（比如指令 Cache 和数据 Cache），即哈弗架构（另一种称为普林斯顿架构）
- 数据冒险：即寄存器数据以来产生的冒险
- 控制冒险：即跳转指令产生的冒险

对于控制冒险，为了加速一般将跳转放在 D 级的 CMP 组件中。

## AT 法解决冲突

课上讲解流水线时并没有采用书上那种麻烦的方式来建模流水线，而是采用了 AT 法。

AT 法中的 A 代表 Address，T 代表 Tuse 和 Tnew。

流水线的核心问题在于两点：何时阻塞？何时转发？

### 何时阻塞

需要阻塞意味着当前需要用到某一个值，而且这个值还没被之前的指令算出来。

因此我们用 Tuse 和 Tnew 来刻画这种情况：
- Tuse：指令进入 D 级后，其后的某个功能部件再经过多少时钟周期就必须要使用寄存器值。对于有两个操作数的指令，其每个操作数的 Tuse 值可能不等（如 store 型指令 rs、rt 的 Tuse 分别为 1 和 2）。
- Tnew：位于 E 级及其后各级的指令，再经过多少周期就能够产生要写入寄存器的结果。在我们目前的 CPU 中，W 级的指令 Tnew 恒为 0；对于同一条指令，Tnew@M = max(Tnew@E - 1, 0)。

显然，需要阻塞的时候就是 `Tuse < Tnew` 的情况。

### 何时转发

需要转发转发意味着一个数据已经被算出来了，但是在后面的数据路径中。

显然，转发要满足两个条件：
- 数据已经算出来了
- 当前需要后面的数据

但是根据阻塞我们知道，如果后面的数据还没算出来，我们又要用，就一定会阻塞。所以在存在阻塞的情况下，第一个条件一定会满足，我们只需要考虑第二个条件就好了。也就是后面写入寄存器的地址和当前用到寄存器的地址相同（注意，地址为 `$0` 时不转发）。