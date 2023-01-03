---
layout: "post"
title: "「BUAA-CO-Lab」 P4 单周期 CPU - 2"
subtitle: "用 Verilog 建模单周期 CPU"
author: "roife"
date: 2020-11-19
tags: ["北航计算机组成实验@课程相关", "课程相关@Tags", "体系结构@Tags", "Verilog@编程语言", "集成电路@Tags", "CPU@体系结构"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

> 本教程写于 2020 年，可能已经过时，请仔细甄别内容时效性。如有问题可在评论区指出

# 上机总结

和 P3 差不多，仔细看 RTL。总的来说感觉最好课下好好练练 verilog，课上写得时候感觉有点手生，或许是因为不如电路那么直观。但是在写复杂逻辑的时候不用连电路了确实很好。

- 第一题：`bsoal`

  感觉这个指令是全场最难（溜）。需要熟悉组合电路的 `always @(*)` 写法，或者直接用 `function`。

  当寄存器值有奇数个 $1$ 的时候跳转。

  $$
    \begin{aligned}
        & \operatorname{if}\ \operatorname{has\_odd\_one\_bits}(GRF[rs])\ \operatorname{then} \\
        & \qquad PC = PC + 4 + \operatorname{sign\_ext}(offset || 0^2) \\
        & \qquad GRF[31] = PC + 4 \\
        & \operatorname{else} \\
        & \qquad PC = PC + 4
    \end{aligned}
  $$

- 第二题：`xor`

  就是需要加一个高小鹏 PDF 的 `xor`，居然出了原题，这应该是全场最简单的了。

- 第三题：`swrr`

  向右循环位移，有点类似 `sw`。注意好好看题！题目要求 `$display()` 要字对齐。

    $$
    \begin{aligned}
        & Addr \leftarrow GPR[base] + \mathtt{sign\_ext}(offset) \\
        & temp \leftarrow Addr_{1..0} \\
        & \operatorname{if}\ temp == 0\ \operatorname{then} \\
        & \qquad mem_{addr} \leftarrow GRF[rt] \\
        & \operatorname{else} \\
        & \qquad mem_{addr} \leftarrow GRF[rt]_{8*temp - 1 \cdots 0}||GRF[rt]_{31 \cdots 8*temp}
    \end{aligned}
    $$

课下一定要模块化，课上不要慌！（我课上因为失误，第三题拖了好长时间）

最重要的是拿到指令先去和写过的找共同点，分析要用哪些部件。然后按照套路添加即可。

还有就是课下好好做 P5，那你会发现 P4 真是太简单了。

# 课下总结

**一定要多做测试**

直接翻译 P3 电路就可以了，会出问题的地方基本上是 Verilog 的问题。

本人在连接的过程中遇到的几个问题分享一下：
1. 注意阻塞赋值和非阻塞赋值的问题！
2. Debug 的时候可以强行进行综合，然后看看编译器挑了哪些错，注意 Warnings
3. 学长说考题还是跳转+计算+访存，或者是跳转+简单计算+复杂计算。可以试试看英文指令集中比较难的几个指令
4. 准备（或者白嫖）一个自动化测试工具。
5. 注意 verilog 中如果打了 typo，可能会被编译器认为是一条 wire，但是慎用 `` `default net_type none`` ，如果用了必须在所有的端口显式声明 `wire`。

加指令步骤（类似 p3）：考虑要用哪些部件（和 r/i/j/b/l 比较一下，类似于哪个），然后把数据通路连上。可以先在各个元件里完成各自要做的功能，然后再连全局的数据通路。最后在 CU 里添加控制信号。

# 课下实现

电路类似于 P3 分成了 IFU，NPC，EXT，CMP，DM，GRF，CU，主电路。

有一点小更改就是 PC + IM = IFU，然后多了一个 CMP 元件接到 NPC 上，用于处理所有 branch 指令的情况。

DM 的设计也不太一样，可以直接这么写：

{% raw %}

```verilog
// 读取
assign DMout = (DMType == `DM_w) ? `word :
                (DMType == `DM_h) ? {{16{`half_sign}}, `half} :
                (DMType == `DM_hu) ? {{16{1'b0}}, `half} :
                (DMType == `DM_b) ? {{24{`byte_sign}}, `byte} :
                (DMType == `DM_bu) ? {{24{1'b0}}, `byte} :
                32'b0;
// 写入
if (DMType == `DM_w) begin
    `word <= WD;
    $display("%d@%h: *%h <= %h", $time, pc, addr, WD);
end else if (DMType == `DM_h) begin
    `half <= WD[15:0];
    $display("%d@%h: *%h <= %h", $time, pc, addr, WD[15:0]);
end else if (DMType == `DM_b) begin
    `byte <= WD[7:0];
    $display("%d@%h: *%h <= %h", $time, pc, addr, WD[7:0]);
end
```

{% endraw %}

具体看我 GitHub 仓库 [BUAA-CO] 的代码。

## Debug 工具

写了一个用于实时反汇编指令的 module，详情见 [DASM](https://github.com/roife/dasm)。
