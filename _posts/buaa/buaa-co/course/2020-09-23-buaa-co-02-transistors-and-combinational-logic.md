---
layout: "post"
title: "「BUAA-CO」 02 晶体管和组合逻辑"
subtitle: "晶体管，门电路，卡诺图"
author: "roife"
date: 2020-09-23

tags: ["北航计算机组成理论@课程相关", "课程相关@Tags", "Digital Design and Computer Architecture@读书笔记", "读书笔记@Tags", "体系结构@Tags", "集成电路@Tags", "数字电路@集成电路"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 数字电路

## 电平

一般定义驱动源输出高电压（$V_{OH} \sim V_{DD}$）时为高电平，输出低电压（$GND \sim V_{OL}$）为低电平。

对于输入端，$V_{IH} \sim V_{DD}$ 为高电平，$GND \sim V_{IL}$ 为低电平。

电流的传播过程可能会混杂一定的噪声，因此需要定义部分区域以容纳噪声，即噪声容限（noise margin）。
如 $V_{IL} \sim V_{IH}$ 之间被设置为禁止区域，无法预测行为。

## CMOS

MOS 可以作为电子开关使用，一个 MOS 元件由三部分组成：gate，source，drain。

MOS 可以分为两种，nMOS 和 pMOS。

![mos](/img/in-post/post-buaa-co/mos.png "mos"){:height="600px" width="600px"}

其中 nMOS 类似于 NPN 三极管，pMOS 类似于 PNP 三极管。对于 nMOS，当在 gate 施加高电压时，source 和 drain 就可以导通，电流可以流过。pMOS 恰好相反，当在 gate 施加高电压时开关关闭。

nMOS 对于低电平的导通效果较好，pMOS 对于高电平的导通效果较好。

由于 nMOS 需要 p 型 substrate，pMOS 需要 n 型 substrate，所以可以将其做到一起，称为 CMOS（complementary MOS）。

### 用 CMOS 搭建门电路

例如搭建一个 NAND 门：

![cmos-nand](/img/in-post/post-buaa-co/cmos-nand.png "cmos-nand"){:height="200px" width="200px"}

| $A$ | $B$ | 下拉网络 | 上拉网络 | $Y$ |
|-----|-----|----------|----------|-----|
| 0   | 0   | OFF      | ON       | 1   |
| 0   | 1   | OFF      | ON       |     |
| 1   | 0   | OFF      | ON       | 1   |
| 1   | 1   | ON       | OFF      | 0   |

所以含反向逻辑的电路都可以用 pMOS 上拉网络（对 1 导通性好）和 nMOS 下拉网络（对 0 导通性好）组成。

![反向逻辑门的通用结构](/img/in-post/post-buaa-co/inverting-logic-gate-form.png "inverting-logic-gate-form"){:height="200px" width="200px"}

一般来说，pMOS 和 nMOS 网络必然一个串联，一个并联，以防止产生短路和浮空状态。

### 传输门

nMOS 可以导通 0，pMOS 可以导通 1。二者结合可以实现传输门。当 $EN = 1$ 或 $\overline{EN} = 0$ 时传输门可以导通。

![传输门](/img/in-post/post-buaa-co/transmission-gate.png "transmission-gate"){:height="200px" width="200px"}

### 类 nMOS 逻辑

pMOS 速度较慢，并且并联速度大于串联速度，所以一般用类 nMOS 逻辑实现 pMOS 上拉网络。

其中上拉网络的 pMOS 被替换为一个始终导通的弱 pMOS（被称为弱上拉，weak pull-up）。当所有 nMOS 晶体管都不导通时，弱上拉 pMOS 可以维持高电平，否则弱上拉 pMOS 将输出下拉到逻辑 0。

类 nMOS 可以构造存储器或者 PLA。但是当输出低电平时，电源和地面产生短路，此时会持续消耗能量。

![类 nMOS 门](/img/in-post/post-buaa-co/pseudo-nmos-gate.png "pseudo-nmos-gate"){:height="250px" width="250px"}

# 逻辑运算

逻辑运算可以用门电路实现。

## 真值表

真值表转布尔表达式有两种方法：

1. Sum of Products（SoP）看结果为 $1$ 的行：如 $c = \overline{a} b + \overline{b} a$
2. Product of Sums（PoS）看结果为 $0$ 的行：如 $c = (a + b)(\overline{a} + \overline{b})$

## 等值演算

合理利用等值演算可以化简电路，降低成本。

| Theorem                                                                                 | Dual                                                                                | Name                |
|-----------------------------------------------------------------------------------------|-------------------------------------------------------------------------------------|---------------------|
| $B \cdot 1 = 1$                                                                         | $B + 0 = B$                                                                         | Identity            |
| $B \cdot 0 = 0$                                                                         | $B + 1 = 1$                                                                         | Null Element        |
| $B \cdot B = B$                                                                         | $B + B = B$                                                                         | Idempotency         |
| $\overline{\overline{B}} = B$                                                           |                                                                                     | Involution          |
| $B \cdot \overline{B} = 0$                                                              | $B + \overline{B} = 1$                                                              | Complements         |
| $B \cdot C = C \cdot B$                                                                 | $B + C = C + B$                                                                     | Commutativity       |
| $(B \cdot C) \cdot D = B \cdot (C \cdot D)$                                             | $(B + C) + D = B + (C + D)$                                                         | Associativity       |
| $(B \cdot C) + (B \cdot D) = B \cdot (C + D)$                                           | $(B + C) \cdot (B + D) = B + (C \cdot D)$                                           | Distributivity      |
| $B \cdot (B + C) = B$                                                                   | $B + (B \cdot C) = B$                                                               | Covering            |
| $(B \cdot C) + (B \cdot \overline{C}) = B$                                              | $(B + C) \cdot (B + \overline{C}) = B$                                              | Combining           |
| $(B \cdot C) + (\overline{B} \cdot D) + (C \cdot D) = B \cdot C + \overline{B} \cdot D$ | $(B + C) \cdot (\overline{B} + D) \cdot (C + D) = (B + C) \cdot (\overline{B} + D)$ | Consensus           |
| $\overline{B_{0} \cdot B_{1} \cdots} = (\overline{B_{0}} + \overline{B_{1}} + \cdots)$  | $B_{0} + B_{1} + \cdots = (\overline{B_{0}} \cdot \overline{B_{1}} \cdot \cdots)$            | De Morgan’s Theorem |

## 表达式化简（卡诺图）

等式化简既可以使用等值演算，也可以使用卡诺图（Karnaugh Maps）。

![卡诺图画圈](/img/in-post/post-buaa-co/karnaugh-maps.png "karnaugh-maps"){:height="300px" width="300px"}

步骤：
1. 作出卡诺图
2. 画圈
3. 将每个圈的表达式写出来，然后用 or 连接

### 特点

卡诺图的相邻的格子之间只有一位不同（格雷码），因此相邻都为 $1$ 时可以在表达式中消去变量。

### 画圈要求

- 圈尽量少，尽量大，且只能包含 $1$
- 可以环绕卡诺图的边界（所以要注意边角的情况）
- 每个圈的边长必须是 $2$ 的整数次幂
- 可以重复圈一个 $1$（幂等律）

### 无关项

电路中如果有部分输出为无关项，那么可以将其标记为 `x`（不同于非法值），在卡诺图中既可以当作 `0` 也可以当作 `1` 使用。

## X 和 Z

除了 `0` 和 `1` 以外，电路中还有可能出现 `X` 和 `Z`。

- `X` 代表非法值，如结点同时被 `0` 和 `1` 驱动导致处于禁止区域，或者电路仿真中未设置初始值
- `Z` 代表浮空值，即没有被高电平或低电平驱动（注意不同于低电平）

# 组合逻辑

## 多路复用器（multiplexer，MUX）

MUX 有多个输入接口，一个选择输入接口和一个输出接口。输出会根据选择信号在输入数据中选择一个输出。

一个 2:1 MUX 的逻辑表达式可以表示为 $Y = D_{0} \overline{S} + D_{1} S$

![2-1-mux](/img/in-post/post-buaa-co/2-1-mux.png "2-1-mux"){:height="200px" width="200px"}

更多位的 MUX 可以通过基础的 MUX 实现。

![4-1-mux](/img/in-post/post-buaa-co/4-1-mux.png "4-1-mux"){:height="200px" width="200px"}

利用多位 mux 也可以实现任意逻辑表达式，因为 mux 起到了一个单值函数的作用，只要将对应的结果作为输入数据，就可以通过改变选择信号来输出特定的输入数据。

## 译码器（Decoder）

Decoder 有 n 个输入和 $2^n$ 个输出，将输入译为独热编码（One-Hot Code）。

### 独热编码

$n$ 位二进制的 One-Hot Code 为 $2^n$ 位，其中每个 One-Hot Code 都仅有一位为 $1$，从低到高对二进制重新编码。
如 $101$ 的 One-Hot Code 为 $00100000$（从低到高第五位为 $1$）。

### 实现与作用

对于 n:m 的 decoder，只要将输出接口的独热编码解码后，将 `1` 直接连接，将 `0` 取非，再全部连接到一个与门即可。

![decoder](/img/in-post/post-buaa-co/decoder.png "decoder"){:height="300px" width="300px"}

类似于 MUX，Decoder 可以和或门组合实现任意逻辑函数，因为 decoder 可以把任意输入编码到唯一输出，所以只要将为 `1` 的几个输出用或门连接即可。

### Multiplexer 和 Decoder 的区别

- Decoder 的输出均为一位，Multiplexer 可以一个脚输出多位
- Decoder 为一个输入，$n$ 个输出；Multiplexer 为 $n+1$ 输入，一个输出；Demultiplexer 为 $1+1$ 个输入，$n$ 个输出

# 组合逻辑的时序与延迟

在门电路中，输出对输入的响应需要一定时间，因而会造成一定延迟。

## 传播延迟和最小延迟

- 传播延迟（propagation delay）$t_{pd}$ 指输出随输入变化后稳定的下来所需的时间
- 最小延迟（contamination delay）$t_{cd}$ 指输出随输入开始变化的时间

![propagationand-contamination-delay](/img/in-post/post-buaa-co/propagationand-contamination-delay.png "propagationand-contamination-delay"){:height="320px" width="320px"}

$t_{pd}$ 由电路的关键路径（critical path）决定，即由最慢最长的路径决定，其值为 $\sum (t_{pd})_{i}$。

$t_{cd}$ 由电路的最短路径（short path）决定，即最短最快的路径决定，其值为 $\sum (t_{cd})_{i}$。

![critical-path-and-short-path](/img/in-post/post-buaa-co/critical-path-and-short-path.png "critical-path-and-short-path"){:height="600px" width="600px"}

## 毛刺

由于延迟的存在，信号到达元器件的时间可能有时间差。在这一段时间差之间，元器件的输入信号会发生变化，因而可能会导致其输出改变，产生意外的结果，即产生毛刺（glitch）。

![glitch](/img/in-post/post-buaa-co/glitch.png "glitch"){:height="450px" width="450px"}

为了去除毛刺，可以尝试改变门电路，通过添加冗余项来避免毛刺，但是可能会增加成本。

![glitch-2](/img/in-post/post-buaa-co/glitch-2.png "glitch-2"){:height="300px" width="300px"}

# 参考资料

1. *Digital Design and Computer Architecture 2nd*, Chapter 1
2. *Digital Design and Computer Architecture 2nd*, Chapter 2
