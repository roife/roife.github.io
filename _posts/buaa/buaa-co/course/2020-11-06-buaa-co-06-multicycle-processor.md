---
layout: "post"
title: "「BUAA-CO」 06 多周期 CPU"
subtitle: "多周期 CPU 结构与原理"
author: "roife"
date: 2020-10-12
tags: ["北航计算机组成理论@课程相关", "课程相关@Tags", "Digital Design and Computer Architecture@读书笔记", "读书笔记@Tags", "体系结构@Tags", "集成电路@Tags", "Verilog@编程语言", "CPU@体系结构"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 多周期处理器

多周期处理器的思想是，一个指令可以被划分为“取指令、译码/读操作数、执行（ALU 计算）、访存、回写五个阶段”，而且不同指令的五个阶段之间相互独立，所以可以把每个指令拆分成多个阶段，让耗费时间多的指令多执行阶段，而其他指令不需要执行没必要的阶段，从而加快处理器的效率。（注意，并没有同时执行两条指令，因此和流水线不一样）

为了保持不同阶段之间相互独立，需要在不同的状态元件之间插入寄存器，防止上个阶段的值对这个阶段产生干扰。

在 *Digital Design and Computer Architecture* 这本书中，还让 IM 和 DM 合一成为 I/DM，并且减少了 ALU 的数量，只用了一个全局的 ALU。

# 数据路径

## lw

首先先计算出指令的地址，类似于单周期处理器，这里使用一个 `IRWrite` 信号来控制指令的输出。

![multi-lw-address](/img/in-post/post-buaa-co/multi-lw-address.png "multi-lw-address"){:height="700px" width="700px"}

然后将数据读出，并且写到寄存器中。注意，这里使用一个 `IorD` 信号控制是读出指令还是数据。

![multi-lw-load](/img/in-post/post-buaa-co/multi-lw-load.png "multi-lw-load"){:height="700px" width="700px"}

最后计算 NPC。由于这里只用了一个 ALU，所以需要加上 `ALUSrcA` 控制运算路径，用 `ALUSrcB` 控制运算数，用 `PCWrite` 控制 PC 的写入。
注意这里 ALU 的输出直接连接到 ALUResult 而不是 ALUOut，因为这个 PC 计算并不是“执行”阶段的部分。

![multi-lw-npc](/img/in-post/post-buaa-co/multi-lw-npc.png "multi-lw-npc"){:height="700px" width="700px"}

## sw

`sw` 多一个写会 I/DM 的步骤，同时用一个 `MemWrite` 信号控制写入。

![multi-sw](/img/in-post/post-buaa-co/multi-sw.png "multi-sw"){:height="700px" width="700px"}

## R-type

R-type 指令增加一个“寄存器写入地址”并且将 ALU 的结果作为写入数据，前者用 `RegDst` 控制，后者用 `MemtoReg` 控制。同时在 ALU 的输入中多一路选择。

![multi-r-type](/img/in-post/post-buaa-co/multi-r-type.png "multi-r-type"){:height="700px" width="700px"}

## beq

beq 命令的路径可以分为两部分。

上部是控制写入的信号，当两个数相减为 `0` 时表示跳转，此时将 `PCEn` 置 `1`。

下部时 `PC` 地址：首先将 $PC' = PC + 4$ 写入 PC，然后再利用一个执行周期计算 $PC' + Imm*4$，结果放在 ALUOut 中。

![multi-beq](/img/in-post/post-buaa-co/multi-beq.png "multi-beq"){:height="700px" width="700px"}

# 多周期控制

多周期处理器的难点在于 CU 的设计上。单周期 CU 是一个组合电路，但是多周期的 CU 是一个 FSM。

## Fetch

所有指令的第一步都是取出 `PC` 对应的指令，并且将下一条指令（$PC+4$）写入到 `PC` 中。

注意此时 $PC+4$ 并没有经过 ALUOut 寄存器，否则需要慢一个周期。

![multi-control-fetch](/img/in-post/post-buaa-co/multi-control-fetch.png "multi-control-fetch"){:height="700px" width="700px"}

## Decode

第二步是读取寄存器文件，并且对命令进行译码，同时扩展单元对符号数进行扩展。这一步不需要控制信号，但是此时根据 opcode 和 funct 会产生多种路径。

![multi-control-decode](/img/in-post/post-buaa-co/multi-control-decode.png "multi-control-decode"){:height="700px" width="700px"}

## Excute

### lw/sw

首先准备好 ALU 的输入数据，并且计算结果存在 ALUOut 中。

![multi-control-lw-sw-addr](/img/in-post/post-buaa-co/multi-control-lw-sw-addr.png "multi-control-lw-sw-addr"){:height="700px" width="700px"}

#### lw

如果是 lw，则控制存储器读取 ALUOut 对应的数据，将结果存到 Data 寄存器中。

最后一步再将 Data 寄存器中的数据写入 GRF。

![multi-control-lw-memory-read](/img/in-post/post-buaa-co/multi-control-lw-memory-read.png "multi-control-lw-memory-read"){:height="500px" width="500px"}

#### sw

对于 sw，直接控制存储器将数据写入 ALUOut 对应的地址。

![multi-control-lw-write](/img/in-post/post-buaa-co/multi-control-lw-write.png "multi-control-lw-write"){:height="500px" width="500px"}

### R-type

对于 R-type，首先计算出 ALU 的结果并存储到 ALUOut 中。然后将 ALUOut 写入 GRF 中。

![multi-control-r-type](/img/in-post/post-buaa-co/multi-control-r-type.png "multi-control-r-type"){:height="500px" width="500px"}

### beq

对于 beq 指令，注意到在 S0 状态中已经计算了 $PC+4$ 并且存在了 PC 中。所以在 S1（注意到此时并没有什么事做）时可以控制 ALU 输入 PC 和扩展后的 Imm 进行相加，将结果存到 ALUOut 中。

如果指令不是 beq，则不需要管 ALUOut，如果是 beq 则将指令写回 PC。

![multi-control-beq](/img/in-post/post-buaa-co/multi-control-beq.png "multi-control-beq"){:height="500px" width="500px"}

# 更多指令

## addi

addi 指令不需要添加数据通路，只需要修改控制器即可。

addi 指令用两个状态完成。第一个状态计算寄存器 A 和 Imm 相加的值，然后存到 ALUOut 中。第二个阶段将值写回 GRF。

![multi-control-addi](/img/in-post/post-buaa-co/multi-control-addi.png "multi-control-addi"){:height="700px" width="700px"}

## j

j 指令需要 PC 的高四位和 Imm 进行拼接，并且将结果左移 2 位。这个过程可以用一个状态完成。

![multi-j](/img/in-post/post-buaa-co/multi-j.png "multi-j"){:height="700px" width="700px"}

![multi-control-j](/img/in-post/post-buaa-co/multi-control-j.png "multi-control-j"){:height="700px" width="700px"}

# 性能分析

多周期 CPU 的性能取决于各个指令的使用频率。对于使用状态数少的指令执行可以更快。
如果忽略寄存器文件和写存储器的耗时，可以发现关键路径为：

$$T_c = t_{pcq} + t_{mux} + \max(t_{ALU} + t_{mux}, t_{mem}) + t_{setup}$$

注意，多周期处理器需要更多的寄存器和 mux，所以往往并没有比单周期快非常多。

# 课上

课上为了简洁所以不复用 ALU 和存储器。

![multi-data-path](/img/in-post/post-buaa-co/multi-data-path.png "multi-data-path"){:height="700px" width="700px"}

将一个周期分为多个段，每一段包含 “寄存器输出，组合逻辑，寄存器写入” 三部分。
每条指令的 CPI（cycle per instruction）不同，因此时钟频率可以更高。

理念：能尽早算的就尽早算，即使用不到也可以先算出来放寄存器中。

### 最终电路

![multi-rtl](/img/in-post/post-buaa-co/multi-rtl.png "multi-rtl"){:height="700px" width="700px"}

## 控制信号建模

类似于书上，先建模一个 FSM。

![multi-control-model](/img/in-post/post-buaa-co/multi-control-model.png "multi-control-model"){:height="700px" width="700px"}

![multi-control-fsm](/img/in-post/post-buaa-co/multi-control-fsm.png "multi-control-fsm"){:height="700px" width="700px"}

相比于 *Digital Design and Computer Architecture*，课上建模的 CU 状态更简单，但是需要根据不同的指令进行判断转移方式。即教科书根据指令的分类进行转移，课上根据指令执行的阶段进行转移。

使用 verilog 进行实现时，可以用 `PCWr = S1 + (beq & Zero & S3) + (jal & S2)` 实现。
