---
layout: "post"
title: "「BUAA-CO-Lab」 P3 单周期 CPU - 1"
subtitle: "用 Logisim 搭建单周期 CPU"
author: "roife"
date: 2020-11-15

tags: ["北航计算机组成实验@课程相关", "课程相关@Tags", "体系结构@Tags", "集成电路@Tags", "CPU@体系结构"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 上机总结

总的来说并不算很难的上机，前提是你课下做的指令数量足够多，而且结构足够模块化，那么课上只要稍微修改一下就好了。

三道题是跳转 + 计算 + 访存。在上机前我以为指令严格按照三种类型的格式来，上机后发现其实课上的指令并不能严格分类成 R 型或者 I 型，但是大体上形式不会变化太多，所以问题也不大。

做题时一定要好好看 RTL! RTL 比文字描述更简洁直观，课上基本就是把 RTL 翻译成电路。

- 第一题：`balr`

    这是一个类似于 `jalr` 的指令。

    $$PC \leftarrow PC + 4 + \mathtt{sign\_ext}(imm||0^2)$$

    $$GPR[rt] \leftarrow PC + 4$$

- 第二题：`wsbh`

    这个指令在格式上比较类似于移位指令 `sll`，不过不需要用到 shamt。只要稍微修改一下 ALU 就好了。

    $$GPR[rd] \leftarrow GPR[rt]_{23..16}\ ||\ GPR[rt]_{31..24}\ ||\ GPR[rt]_{7..0}\ ||\ GPR[rt]_{15..8}$$

- 第三题：`lbi`

    一个很像 `lb` 的指令，唯一的区别在于需要用到存储器，需要稍微修改一下数据通路。

    $$Addr \leftarrow GPR[base] + \mathtt{sign\_ext}(offset)$$

    $$mem \leftarrow memory[Addr]$$

    $$byte \leftarrow Addr_{1..0}$$

    $$GPR[rt]_{7+8*byte..8*byte} \leftarrow mem_{7+8*byte..8*byte}$$

    课下如果做过了 `jalr`/`sll`/`lb` 那么这三题就是白送的。

加指令方法：先观察 RTL 确定指令类型，找到类似的指令（r/i/b/j），观察主电路要不要添加数据路径（元件要不要添加输入）。为元件添加了相应的输入后，先在各个元件里面完成对应的功能。最后修改 CU。

还有一个经验就是，课上测试一般存在于前几个点，后几个点不涉及课上指令。比如这次第一题只有前三个点用到了题目要求的指令，而后面几个点都没有。所以如果发现自己错了后面几个点，那基本上是课下测试的问题。（此条存疑，请谨慎对待）

# 课下总结

**一定要多做测试**

按照课上说的，将 CPU 分为 NPC，PC，IM，EXT，GRF，ALU，DM 然后依次连起来就好了。

需要注意的有以下几点：
1. nop 指令：不需要在 CU 里面特殊处理
2. 移位指令：需要 shamt，因此要在 ALU 里面加新的接口
3. CU: CU 中可以用 Priority Encoder（Decoder 的逆操作）发出信号
4. 存储指令：对于半字或者位指令，因为 DM 是按字存储的，需要在 DM 的前后都加上组合电路处理读入和输出的数据
5. 跳转指令：注意 jr 是 r-type 指令，jal 和 j 在跳转上使用相同的位
6. 复位：注意同步复位和异步复位的区别，复习 P0
7. 控制信号和 ALUControl 可以多设置几位，方便课上直接连线
8. 学长的经验：课上一般是一个跳转+一个计算+一个访存

我课下实现的指令有 `addu, subu, and, or, sll, sllv, slt, jr / addi, ori, lui, slti / beq, blez / j, jal / sw, sh / lw, lh, lhu`。基本是把每种类型的都做一个，课上心里才有底。

# 课下实现

主要看 *Digital Design and Computer Architecture* 这本书，按照上面的方法搭建 CPU 即可。

## PC

没什么好说的，就是一个寄存器。可能要注意一下复位方式（同步还是异步）。

## NPC

NPC 注意要和 ALU/CU 配合。`beq` 需要 `ALUzero` 这个信号才能使用，但是实际上比较麻烦（比如实现小于转移指令，这里建议或许可以直接用 `ALUout` 代替，因为我们的目标是做题，这样写更方便（溜））。

![P3-lab-npc-0](/img/in-post/post-buaa-co/p3-lab-npc-0.png "p3-lab-npc-0"){:height="500px" width="500px"}

![P3-lab-npc-1](/img/in-post/post-buaa-co/p3-lab-npc-1.png "p3-lab-npc-1"){:height="500px" width="500px"}

## IM

IM 用 ROM 实现，注意截掉最低两位。

![P3-lab-IM](/img/in-post/post-buaa-co/p3-lab-im.png "p3-lab-im"){:height="500px" width="500px"}

## SPLT

为了方便取位而设置的一个元件。

![P3-lab-splt](/img/in-post/post-buaa-co/p3-lab-splt.png "p3-lab-splt"){:height="300px" width="300px"}

## EXT

为了方便，EXT 一般需要一个 `EXTOp` 信号控制扩展方式。

![P3-lab-ext](/img/in-post/post-buaa-co/p3-lab-ext.png "p3-lab-ext"){:height="500px" width="500px"}

## GRF

耐心点排线，推荐写代码生成元件。这里是一个例子。

```cpp
for (int i=0; i<=31; ++i) {
    int x = X, y = Y + i * 30;
    printf("<comp lib=\"0\" loc=\"(1540,%d)\" name=\"Tunnel\">\n", y);
    printf("<a name=\"width\" val=\"32\"/>\n");
    printf("<a name=\"label\" val=\"i%d\"/>\n", i);
    printf("</comp>\n");
}
```

![P3-lab-grf-0](/img/in-post/post-buaa-co/p3-lab-grf-0.png "p3-lab-grf-0"){:height="500px" width="500px"}

![P3-lab-grf-1](/img/in-post/post-buaa-co/p3-lab-grf-1.png "p3-lab-grf-1"){:height="500px" width="500px"}

![P3-lab-grf-2](/img/in-post/post-buaa-co/p3-lab-grf-2.png "p3-lab-grf-2"){:height="700px" width="700px"}

## ALU

相对比较好做，可以先写个支持加减与或的，然后慢慢扩展。

![P3-lab-alu-0](/img/in-post/post-buaa-co/p3-lab-alu-0.png "p3-lab-alu-0"){:height="500px" width="500px"}

![P3-lab-alu-1](/img/in-post/post-buaa-co/p3-lab-alu-1.png "p3-lab-alu-1"){:height="500px" width="500px"}

## DM

使用 RAM，注意输入要截掉两位地址。

![P3-lab-dm](/img/in-post/post-buaa-co/p3-lab-dm.png "p3-lab-dm"){:height="500px" width="500px"}

## MW/MR

如果你也做了半字/字节的存储指令，那么一般需要这两个电路对写入数据进行预处理（MW），并且处理 DM 输出的数据（MR）。

### MR

![P3-lab-mr-0](/img/in-post/post-buaa-co/p3-lab-mr-0.png "p3-lab-mr-0"){:height="300px" width="300px"}

![P3-lab-mr-1](/img/in-post/post-buaa-co/p3-lab-mr-1.png "p3-lab-mr-1"){:height="300px" width="300px"}

### MW

![P3-lab-mw-0](/img/in-post/post-buaa-co/p3-lab-mw-0.png "p3-lab-mw-0"){:height="500px" width="500px"}

![P3-lab-mw-1](/img/in-post/post-buaa-co/p3-lab-mw-1.png "p3-lab-mw-1"){:height="500px" width="500px"}

## CU

建议用这种模块化的方式做，更容易加指令。

![P3-lab-cu-0](/img/in-post/post-buaa-co/p3-lab-cu-0.png "p3-lab-cu-0"){:height="500px" width="500px"}

![P3-lab-cu-1](/img/in-post/post-buaa-co/p3-lab-cu-1.png "p3-lab-cu-1"){:height="700px" width="700px"}

![P3-lab-cu-2](/img/in-post/post-buaa-co/p3-lab-cu-2.png "p3-lab-cu-2"){:height="600px" width="600px"}
