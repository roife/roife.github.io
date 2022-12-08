---
layout: "post"
title: "「BUAA-CO」 04 数字模块"
subtitle: "基础数字模块组成"
author: "roife"
date: 2020-10-10
tags: ["北航计算机组成理论@课程相关", "课程相关@Tags", "Digital Design and Computer Architecture@读书笔记", "读书笔记@Tags", "体系结构@Tags", "集成电路@Tags", "Verilog@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 算术电路

## 加法

### 半加器与全加器

半加器是能执行一位加法的器件，其中输入为 $A$，$B$，输出为 $S$，$C_{out}$ 表示进位。

$$S = A \oplus B$$

$$C_{out} = AB$$

![半加器](/img/in-post/post-buaa-co/half-adder.png "half-adder"){:height="200px" width="200px"}

全加器相对于半加器多了一个输入 $C_{in}$ 表示接收的进位。

$$S = A \oplus B \oplus C$$

$$C_{out} = AB + AC_{in} + BC_{in}$$

![半加器](/img/in-post/post-buaa-co/half-adder.png "half-adder"){:height="200px" width="200px"}

### 进位传播加法器

进位传播加法器（Carry Propagate Adder，CPA）能对两个 $n$ 位数进行加法运算。

#### 行波进位加法器

行波进位加法器（ripple-carry adder）由加法器简单地连接得到，速度较慢，延迟线性增长。

![行波进位加法器](/img/in-post/post-buaa-co/ripple-carry-adder.png "ripple-carry-adder"){:height="400px" width="400px"}

#### 先行进位加法器

先行进位加法器（Carry-Lookahead Adder，CLA）将加法电路分块，同时使得每一块中尽快产生进位信号。

CLA 用产生信号 $G$ 和传播信号 $P$ 来描述进位。
- 在不考虑进位的情况下，如果某一位必然产生进位，则发出 $G_i$ 信号，即 $G_i = A_i B_i$
- 在考虑进位的情况下，如果某一位可以产生进位，则发出 $P_i$ 信号，即 $P_i = A_i + B_i$

用 $G_i$ 和 $P_i$ 重写进位逻辑，可以得到：

$$C_i = G_i + P_i C_{i-1}$$

将其扩展到多块，定义 $G_{i:j}$ 和 $P_{i:j}$ 为第 $i~j$ 列块的产生信号和传播信号。
- 块产生 $G$ 信号的条件：当最高有效列发出 $G$ 信号，或者最高有效列发出 $P$ 信号且前面产生了进位，则这一块产生进位，即 $G_{3:0} = G_3 + P_3 (G_2 + P_2 (G_1 + P_1 G_0))$
- 块产生 $P$ 信号的条件：块中所有为都能产生 $P$ 信号，即 $P_{3:0} = P_3 P_2 P_1 P_0$

用 $G_{i:j}$ 和 $P_{i:j}$ 重写进位逻辑，可以得到：

$$C_i = G_{i:j} + P_{i:j} C_j$$

![32 位 CLA](/img/in-post/post-buaa-co/32-bit-cla.png "32-bit-cla"){:height="500px" width="500px"}

所有的 CLA 块可以同时计算 $G$ 信号和 $P$ 信号。关键路径从 $G_0$ 开始。

令 $t_pg$ 为产生 $G_i$ 和 $P_i$ 的单个逻辑门的延迟 ，$t_{pg\\\_block}$ 为 $k$ 位块中产生 $P_{i:j}$ 和 $G_{i:j}$ 的延迟，$t_{AND\\\_OR}$ 为从 $C_{in}$ 到 $C_{out}$ 到达 $k$ 位 CLA 的最后的 AND/OR 逻辑的延迟，计算延迟可得：

$$t_{CLA} = t_{pg} + t_{pg\\\_block} + (\frac{N}{k} - 1)t_{AND\\\_OR} + k t_{FA}$$

可以发现，虽然 CLA 快很多，但是延迟还是线性增长的。

#### 前缀加法器

前缀加法器（Prefix Adder，PA）首先计算 2 位的块，然后计算 4 位的块，接着计算 8 的块，直到计算完成。

$$S_i = (A_i \oplus B_i) \oplus C_{i-1}$$

定义 $i = -1$ 表示 $C_{in}$ 的列，则 $G_{-1} = C_{in}$，$P_{-1} = 0$，$C_{i-1} = G_{i-1:-1}$。可得：

$$S_i = (A_i \oplus B_i) \oplus G_{i-1|-1}$$

接下来要快速计算 $G_{-1:-1}, G_{0:-1}, G_{1:-1}, \dots, G_{N-2:-1}$ 以及 $P_{-1:-1}, P_{0:-1}, P_{1:-1}, \dots, P_{N-2:-1}$。PA 首先用 AND 和 OR 门进行预计算产生 $P_i$ 和 $G_i$ 信号。然后利用 上部分 $i:k$ 以及下部分 $k-1:j$ 计算 $i:j$ 位的 $G_{i:j}$ 和 $P_{i:j}$。

$$G_{i:j} = G_{i:k} + P_{i:k} G_{k-1:j}$$

$$P_{i:j} = P_{i:k} P_{k-1:j}$$

![32 位 PA](/img/in-post/post-buaa-co/32-bit-pa.png "32-bit-pa"){:height="600px" width="600px"}

N 位前缀加法器的关键路径位 $\log_{2}N$ 步的黑色前缀单元获得所有前缀，然后 $G_{i-1:-1}$ 通过底部的 XOR 们计算 $S_i$。

令 $t_{pg\\\_prefix}$ 为黑色前缀单元的延迟，可得：

$$t_{PA} = t_{pg} + \log_{2}N(t_{pg\\\_prefix}) + t_{XOR}$$

可以发现，前缀加法器的延迟以对数增长，但是要消耗更多的硬件。

### 延迟

如在 32 位加法中，假设输入门电路延迟为 $100\mathrm{ps}$，全加器延迟为 $300\mathrm{ps}$。
- 行波进位加法器延迟为 $32 \times 300\mathrm{ps} = 9.6\mathrm{ns}$
- CLA 中
  + $t_{pg} = 100\mathrm{ps}$
  + $t_{pg\\\_block} = 6 \times 100\mathrm{ps} = 600\mathrm{ps}$
  + $t_{AND\\\_OR} = 2 \times 100\mathrm{ps} = 200\mathrm{ps}$
  + 则 $t_{CLA} = 100\mathrm{ps} + 600\mathrm{ps} + (32/4 - 1) \times 200\mathrm{ps} + (4 \times 300\mathrm{ps}) = 3.3\mathrm{ns}$
- PA 中
  + $t_{pg} = 100\mathrm{ps}$
  + $t_{pg\\\_prefix} = 200\mathrm{ps}$
  + 则 $t_{PA} = 100\mathrm{ps} + \log_{2}(32) \times 200\mathrm{ps} + 100\mathrm{ps} = 1.2ns$

## 减法

减去一个数即加上其补码，所以 $A - B = A + \overline{B} + 1$。
在 CPA 中将输入 $B$ 取反，并使 $C_{in} = 1$ 即可计算减法。

![减法器](/img/in-post/post-buaa-co/subtractor.png "subtractor"){:height="250px" width="250px"}

## 比较器

比较器分为相等比较器（equality comparator）和量值比较器（magnitude comparator）。

其中相等比较器直接利用异或门搭建，可以比较两个数字是否相等。

![相等比较器](/img/in-post/post-buaa-co/equality-comparator.png "equality-comparator"){:height="500px" width="500px"}

量值比较器首先计算 $A - B$，然后根据符号位判断关系。

![量值比较器](/img/in-post/post-buaa-co/magnitude-comparator.png "magnitude-comparator"){:height="250px" width="250px"}

## ALU

算术逻辑单元（arithmetic/logical unit，ALU）是多种运算（加、减、比较、AND、OR）的综合，并用一个 $F$ 端口进行控制。

![ALU 符号](/img/in-post/post-buaa-co/alu.png "ALU"){:height="250px" width="250px"}

| $F_{2:0}$ | 功能        | $F_{2:0}$ | 功能                   |
|-----------|-------------|-----------|------------------------|
| 000       | $A\ AND\ B$ | 100       | $A\ AND\ \overline{B}$ |
| 001       | $A\ OR\ B$  | 101       | $A\ OR\ \overline{B}$  |
| 010       | $A+B$       | 110       | $A-B$                  |
| 011       | 未使用      | 111       | SLT                    |

设计电路时可以利用编码的特性，即 $F$ 的最后一位决定了输入 $B$ 的正负。

![ALU](/img/in-post/post-buaa-co/n-bit-alu.png "n-bit-alu"){:height="400px" width="400px"}

## 移位器和循环移位器

移位器一般有三种：
- 逻辑移位器：逻辑左移（LSL）和逻辑右移（LSR）用 0 填补空位
- 算术移位器：算术右移（ASR）时会用最高位填补 MSB
- 循环移位器：将一端的数字填补到另一端

移位器可以用 n 个 n:1 的 MUX 实现。

![Shifters](/img/in-post/post-buaa-co/4-bit-shifters.png "4-bit-shifters"){:height="700px" width="700px"}

![Rotators](/img/in-post/post-buaa-co/4-bit-rotators.png "4-bit-rotators"){:height="500px" width="500px"}

## 乘法

乘法是 AND，移位和加法的综合。

如图，第 $i$ 行为 $B_i\ AND(A_3, A_2, A_1, A_0)$。

![Multiplier](/img/in-post/post-buaa-co/4-bit-multiplier.png "4-bit-multiplier"){:height="800px" width="800px"}

## 除法
```algorithm
R' = 0
for i = N−1 to 0
    R = {R' << 1, Ai}
    D = R − B
    if D < 0 then   Qi = 0, R' = R  // R < B
    else            Qi = 1, R' = D  // R >= B
R = R'
```

$n$ 除法器阵列需要 $n^2$ 个除法器实现。除法器中的 $N$ 端信号表示 $R - B$ 是否为负数，可以从阵列每一行最左端的 $D$ 输出得到，即差的符号位。

![Divider](/img/in-post/post-buaa-co/4-bit-divider.png "4-bit-divider"){:height="500px" width="500px"}

由于 $n$ 为除法器阵列的延迟以 $n^2$ 增长，因此除法非常慢。

# 时序电路

## 计数器

计数器可以直接用加法器和寄存器实现。

![Counter](/img/in-post/post-buaa-co/n-bit-counter.png "n-bit-counter"){:height="250px" width="250px"}

其他类型的计数器（如 UP/DOWN 计数器，加载新值的计数器）都可以据此改造。

```verilog
always @(posedge clk, posedge reset)
    if (reset)  q <= 0;
    else        q <= q + 1;
```

## 移位寄存器

在移位寄存器中，每个时钟上升沿到来时都会从 $S_{in}$ 中读入一位，并且其他位向后移动一位。

![Shift Register](/img/in-post/post-buaa-co/shift-register.png "shift-register"){:height="600px" width="600px"}

类似的有并行移位寄存器，可以一次性读入多位，并慢慢将其移出。

![Shift Register with parellel load](/img/in-post/post-buaa-co/shift-register-with-parellel-load.png "shift-register-with-parellel-load"){:height="700px" width="700px"}

```verilog
always @(posedge clk, posedge reset)
    if (reset)      q <= 0;
    else if (load)  q <= d;
    else            q <= {q[N-2 : 0], sin};
```

### 扫描链

并行移位寄存器可以用于构建测试电路。

由于电路中寄存器数量过多，因此不可能为每一个寄存器都提供输入接口，此时可以用并行移位寄存器一位一位放入数据。

当电路处于工作状态时直接从 D 端读入数据，忽略扫描链。

当电路处于测试状态时，利用触发器串行地移入或移出数据。

![可扫描除法器](/img/in-post/post-buaa-co/scannable-flip-flop.png "scannabl-flip-flop"){:height="800px" width="800px"}
