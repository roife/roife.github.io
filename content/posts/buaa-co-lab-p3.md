+++
title = "[BUAA-CO-Lab] P3 单周期 CPU - 1"
author = ["roife"]
date = 2020-11-15
aliases = ["/posts/2020-11-15-buaa-co-lab-p3"]
series = ["buaa-co"]
tags = ["体系结构"]
draft = false
+++

## 上机总结 {#上机总结}

总的来说并不算很难的上机，前提是你课下做的指令数量足够多，而且结构足够模块化，那么课上只要稍微修改一下就好了。

三道题是跳转 + 计算 + 访存。在上机前我以为指令严格按照三种类型的格式来，上机后发现其实课上的指令并不能严格分类成 R 型或者 I 型，但是大体上形式不会变化太多，所以问题也不大。

做题时一定要好好看 RTL! RTL 比文字描述更简洁直观，课上基本就是把 RTL 翻译成电路。

-   第一题：`balr`

    这是一个类似于 `jalr` 的指令。

    \\[PC \leftarrow PC + 4 + \mathtt{sign\\\_ext}(imm||0^2)\\]

    \\[GPR[rt] \leftarrow PC + 4\\]

-   第二题：`wsbh`

    这个指令在格式上比较类似于移位指令 `sll`，不过不需要用到 shamt。只要稍微修改一下 ALU 就好了。

    \\[GPR[rd] \leftarrow GPR[rt]\_{23..16}\ ||\ GPR[rt]\_{31..24}\ ||\ GPR[rt]\_{7..0}\ ||\ GPR[rt]\_{15..8}\\]

-   第三题：`lbi`

    一个很像 `lb` 的指令，唯一的区别在于需要用到存储器，需要稍微修改一下数据通路。

    \\[Addr \leftarrow GPR[base] + \mathtt{sign\\\_ext}(offset)\\]

    \\[mem \leftarrow memory[Addr]\\]

    \\[byte \leftarrow Addr\_{1..0}\\]

    \\[GPR[rt]\_{7+8\*byte..8\*byte} \leftarrow mem\_{7+8\*byte..8\*byte}\\]

    课下如果做过了 `jalr` / `sll` / `lb` 那么这三题就是白送的。

加指令方法：先观察 RTL 确定指令类型，找到类似的指令（r/i/b/j），观察主电路要不要添加数据路径（元件要不要添加输入）。为元件添加了相应的输入后，先在各个元件里面完成对应的功能。最后修改 CU。

还有一个经验就是，课上测试一般存在于前几个点，后几个点不涉及课上指令。比如这次第一题只有前三个点用到了题目要求的指令，而后面几个点都没有。所以如果发现自己错了后面几个点，那基本上是课下测试的问题。（此条存疑，请谨慎对待）


## 课下总结 {#课下总结}

**一定要多做测试**

按照课上说的，将 CPU 分为 NPC，PC，IM，EXT，GRF，ALU，DM 然后依次连起来就好了。

需要注意的有以下几点：

1.  nop 指令：不需要在 CU 里面特殊处理
2.  移位指令：需要 shamt，因此要在 ALU 里面加新的接口
3.  CU: CU 中可以用 Priority Encoder（Decoder 的逆操作）发出信号
4.  存储指令：对于半字或者位指令，因为 DM 是按字存储的，需要在 DM 的前后都加上组合电路处理读入和输出的数据
5.  跳转指令：注意 jr 是 r-type 指令，jal 和 j 在跳转上使用相同的位
6.  复位：注意同步复位和异步复位的区别，复习 P0
7.  控制信号和 ALUControl 可以多设置几位，方便课上直接连线 8. 学长的经验：课上一般是一个跳转~~一个计算~~一个访存

我课下实现的指令有 `addu, subu, and, or, sll, sllv, slt, jr / addi, ori, lui, slti / beq, blez / j, jal / sw, sh / lw, lh, lhu`。基本是把每种类型的都做一个，课上心里才有底。
