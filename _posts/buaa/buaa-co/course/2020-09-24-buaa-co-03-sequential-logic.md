---
layout: "post"
title: "「BUAA-CO」 03 时序逻辑"
subtitle: "触发器，时序，状态机"
author: "roife"
date: 2020-09-24

tags: ["北航计算机组成理论@课程相关", "课程相关@Tags", "Digital Design and Computer Architecture@读书笔记", "读书笔记@Tags", "体系结构@Tags", "集成电路@Tags", "数字电路@集成电路"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 锁存器与触发器

## RS 锁存器

锁存器是利用输出反馈到输入，并且电路可以形成稳态，从而做到记忆状态量。
RS 锁存器（SR Latch）的 R 端（reset）用于复位结果为 0，S 端（set）用于设置结果为 1。两个端口不应该同时置 1。

| $S$ | $R$ | $Q$        |
|-----|-----|------------|
| 0   | 0   | $Q_{prev}$ |
| 0   | 1   | 0          |
| 1   | 0   | 1          |
| 1   | 1   | N/A        |

RS 锁存器可以用或非门或者与非门两种结构搭建，表达式为 $Q = \overline{R \vert \overline{Q_{prev}}}$ 或者 $Q = \overline{\overline{S} \& \overline{Q_{prev}}}$。

![RS 锁存器](/img/in-post/post-buaa-co/sr-latch.png "SR Latch"){:height="500px" width="500px"}

缺点：RS 锁存器在 S 和 R 端同时生效时输出不能确定，而且不能与 clk 信号同步，所以一般要添加一个 enable 端。

## D 锁存器

D 锁存器（D Latch）在 SR 锁存器的基础上添加了一个 clk 信号，用于控制 SR 锁存器的变化。

![D 锁存器](/img/in-post/post-buaa-co/d-latch.png "D Latch"){:height="300px" width="300px"}

| $CLK$ | $D$ | $\overline{D}$ | $S$ | $R$ | $Q$        |
|-------|-----|----------------|-----|-----|------------|
| 0     | X   | X              | 0   | 0   | $Q_{prev}$ |
| 1     | 0   | 1              | 0   | 1   | 0          |
| 1     | 1   | 0              | 1   | 0   | 1          |

D 锁存器避免了 RS 锁存器的非法状态，同时允许用 clk 信号控制锁存器的状态变化。

缺点：在一个时钟周期内，D 锁存器的输入信号如果多次变化，那么输出信号也会变化（理想是输出结果仅在时钟上升沿改变）。

![D 锁存器的局限性](/img/in-post/post-buaa-co/d-latch-limitation.png "D Latch Limitation"){:height="400px" width="400px"}

## D 触发器

D 触发器（D Flip-Flop）利用一个 D 锁存器作为缓冲，实现了输出仅在时钟上升沿改变的效果。和输入端连接的称为主锁存器（the master latch），和输出端连接的称为从锁存器（the salve latch）。

![D 触发器结构](/img/in-post/post-buaa-co/d-flip-flop-internal.png "D Flip-Flop-internal"){:height="200px" width="200px"}

当 clk 为 0 时，主锁存器随输入信号 D 变化，从锁存器保持不变；当 clk 从 0 变为 1 时，主锁存器停止变化，同时从锁存器获得主锁存器当前的值（即时钟上升沿的值）。

![D 触发器波形](/img/in-post/post-buaa-co/d-flip-flop-wave.png "D Flip-Flop wave"){:height="400px" width="400px"}

### D 触发器的延迟

由于 D 触发器有两个锁存器，因此对于信号保持时间有要求。

![D 锁存器延迟](/img/in-post/post-buaa-co/d-flip-flop-timing.png "D Flip-Flop timing"){:height="600px" width="600px"}

- setup time: 时钟上升沿到来前信号至少要保持的时间（改变主锁存器）
- hold time: 时钟上升沿到来后信号至少要保持的时间（改变从锁存器）
- "CLK-to-Q" Delay: 时钟上升沿到输出信号改变的时间

## 带使能端的触发器

组合 MUX 和触发器可以实现带使能端的触发器（一般不在时钟信号上进行门电路操作，因为可能打乱电路的时序）。

![带使能端的触发器](/img/in-post/post-buaa-co/enabled-flip-flop.png "Enabled Flip-Flop"){:height="200px" width="200px"}

## 带复位端的触发器

带复位端的触发器有两种，同步复位和异步复位。
- 同步复位：仅在时钟上升沿复位
- 异步复位：随时都可以复位（需要改变触发器内部电路，所以下面只考虑同步复位）

![带复位端的触发器](/img/in-post/post-buaa-co/resettable-flip-flop.png "Resettable Flip-Flop"){:height="200px" width="200px"}

带使能端和复位端的触发器结合使用可以作为寄存器。

## 同步时序逻辑

非同步时序电路可能存在竞争（racing，类似于毛刺，但是在时序电路中可能会导致寄存器状态改变）的问题，一般通过在电路中插入寄存器解决。

在同步时序电路中，要求所有时钟信号相同（即不能在时钟信号上使用门电路），并且每一个环路上都有寄存器（防止竞争）。

# 有限状态机

有限状态机（Finite State Machine，FSM）是描述状态及转移的数据模型，由次态逻辑（next state logic），寄存器和输出逻辑（output logic）组成，一般可以分为 Moore 型（输出仅取决于状态）和 Mealy 型（输出取决于输入和状态）。

![Moore 型和 Mealy 型](/img/in-post/post-buaa-co/moore-mealy-internal.png "Moore machines and Mealy machines"){:height="600px" width="600px"}

## 构造 FSM

1. 状态规划（每个状态代表什么意思）
2. 确定主要状态转移，并补充其他转移（不能出现不完备的转移，未定义的状态一般强制转移到初态）
3. 增加复位信号（用来确保数字电路被有效初始化和严格同步）
4. 构造次态逻辑（组合电路）
5. 产生输出信号（需要决定是 Moore 还是 Mealy）

## 状态编码

状态编码一般有三种方案：二进制编码（logN : N），格雷码（logN : N）和独热码（N : N）。
由于 FPGA 的寄存器数量多，所以一般使用独热码提高电路效率和可靠性。（做题的时候可以用二进制编码，状态少，写起来方便）

并且用独热码时可以进行表达式优化，如 $\overline{R3}\ \&\ R2\ \&\ \overline{1}\ \&\ \overline{R0}$ 可以优化为 $R2$。

## Moore 与 Mealy

Moore 和 Mealy 的区别在于，Moore 需要等待状态转移完成后才输出结果（因此会晚一个周期），而 Mealy 在输入的时候可以直接响应。
在 Mealy 中每一种转移受到输入信号影响，所以会在转移上的 `/` 后标注输出。

Mealy 的状态数量可以比 Moore 少一个，因为 Mealy 的输出可以和输入有关。当 Mealy 和 Moore 使用同样的状态设计时，Mealy 的输出可以只有半个周期（因为状态机的状态改变需要一个周期，Moore 需要等到到达最后一个状态，Mealy 则可以在倒数第二个状态的时候直接更新输出，而进入最后一个状态则恢复输出，此时只有半个周期）。

![Moore 型和 Mealy 型的周期区别](/img/in-post/post-buaa-co/moore-mealy-signal-width.jpg){:height="700px" width="700px"}

如一个响应 `01` 信号的电路：

![Moore 型和 Mealy 型的区别](/img/in-post/post-buaa-co/moore-mealy.png "Moore and Mealy"){:height="700px" width="700px"}

具体选择 Moore 还是 Mealy 要看对于输出信号时刻的要求。

## 次态逻辑构造

对于独热码，次态逻辑的构造比较方便，直接将两个状态用线即可。下面主要介绍针对二进制编码（logN : 1）的次态逻辑构造。

|当前状态（$S_2$ $S_1$ $S_0$）| 输入（A）| 下一状态（$S'_2$ $S'_1$ $S'_0$）| 输出（Y）|
|-|-|-|-|
|S0 (000) | 0 | S0 (000) | 0 |
|S0 (000) | 1 | S1 (00**1**) | 0 |
|S1 (001) | 0 | S0 (000) | 0 |
|S1 (001) | 1 | S2 (0**1**0) | 0 |
|S2 (010) | 0 | S3 (0**11**) | 0 |
|S2 (010) | 1 | S2 (0**1**0) | 0 |
|S3 (011) | 0 | S0 (000) | 0 |
|S3 (011) | 1 | S4 (**1**00) | 1 |
|S4 (100) | 0 | S0 (000) | 0 |
|S4 (100) | 1 | S1 (00**1**) | 0 |

对于目标状态的每一位位（$S'_2$ $S'_1$ $S'_0$），提取出其为 1 的情况写出逻辑表达式。

$$
S'_2 = \overline{S_2} S_1 S_0 A
$$

$$
S'_1 = \overline{S_2}\ \overline{S_1} S_0 A + \overline{S_2} S_1 \overline{S_0}\ \overline{A} + \overline{S_2} S_1 \overline{S_0}
$$

$$
S'_0 = \overline{S_2}\ \overline{S_1}\ \overline{S_0} A + \overline{S_2} S_1 \overline{S_0}\ \overline{A} + S_2 \overline{S_1}\ \overline{S_0} A = \overline{S_1}\ \overline{S_0} A + \overline{S_2} S_1 \overline{S_0}\ \overline{A}
$$

$$
Y = \overline{S_2} S_1 S_0 A
$$

## 复位信号

- 异步复位：复位信号有效，则寄存器就被复位（复位信号通常由系统产生，一般仅在上电引起的全局复位时使用）
- 同步复位：复位信号有效且时钟上升沿时才能复位寄存器（复位信号既可以由系统产生，也可以由电路产生。对于后者而言，通常是用于在某个特定状态清除寄存器值）

同步复位可以避免电路中的毛刺产生的复位信号的影响。

## 匹配特定串

匹配特定串的电路可以用寄存器电路和状态机实现，两种方法各有优势。

以下以匹配二进制串 `1101` 为例。在匹配串时可以按照串是否可重叠分为两种匹配模式，如 `1101101` 可以匹配为 `2` 或 `1`。

寄存器实现需要用更多的寄存器，而状态机实现需要更复杂的组合电路设计。

### 寄存器实现

可重叠实现：

![寄存器可重叠实现](/img/in-post/post-buaa-co/1101-register-1.png "1101-register-1"){:height="400px" width="400px"}

不可重叠实现：

![寄存器的可重叠实现](/img/in-post/post-buaa-co/1101-register-2.png "1101-register-2"){:height="400px" width="400px"}

> 思考：如果要求匹配的串是 `0010` 怎么办。（可以将 `0` 预先取反变成 `1111`）。

### 状态机实现

![FSM 可重叠实现](/img/in-post/post-buaa-co/1101-fsm-1.png "1101-fsm-1"){:height="200px" width="200px"}

# 时序逻辑的时序

如前面提到的，时序逻辑有建立时间（setup time）和 保持时间（hold time）的概念。这一段时间统称为 孔径时间（aperture time）。Aperture time 的存在限制了时钟周期必须能使所有信号稳定下来，这也限制了系统的速度。在真实的系统中，时钟不能同步到达所有电路，即发生时钟偏移（clock skew），这进一步限制了时钟周期。

## 动态约束

![同步电路的时序](/img/in-post/post-buaa-co/timing-of-synchronous-sequential-logic.png "timing-of-synchronous-sequential-logic"){:height="400px" width="400px"}

- $t_{setup}$: setup time
- $t_{hold}$: hold time
- $t_{ccq}$: 最小延迟
- $t_{pcq}$: 传播延迟

## 时间约束

### 建立时间约束

![建立时间约束的最大延迟](/img/in-post/post-buaa-co/maximum-delay-for-setup-time-constrain.png "maximum-delay-for-setup-time-constrain"){:height="350px" width="350px"}

显然要求 $T_{e} \geq t_{pcq} + t_{pd} + t_{setup}$，即 $t_{pd} \leq T_{e} - (t_{pcq} + t_{setup})$，这个式子被称为**建立时间约束**，确定了设计组合电路的最大传播延迟。

### 保持时间约束

![保持时间约束的最大延迟](/img/in-post/post-buaa-co/minimum-delay-for-hold-time-constraint.png "minimum-delay-for-hold-time-constraint"){:height="350px" width="350px"}

显然要求 $t_{ccq} + t_{cd} \geq t_{hold}$，即 $t_{cd} \geq t_{hold} - t_{ccq}$，这个式子被称为**保持时间约束**，确定了设计组合电路的最大最小延迟。

假设没有组合电路，即两个寄存器直接相连，那么令 $t_{cd} = 0$，可以得到 $t_{hold} \leq t_{ccq}$，即可靠寄存器的保持时间总是小于最小延迟。

## 时钟偏移

线路长度，噪声，门控电路都有可能造成时钟偏移。

![带时钟偏移的保持时间约束](/img/in-post/post-buaa-co/setup-time-constraint-with-clock-skew.png "setup-time-constraint-with-clock-skew"){:height="500px" width="500px"}

其中黑粗线表示时钟到达的最晚时间。

类似地，可以得到 $t_{pd} \leq T_{e} - (t_{pcq} + t_{setup} + t_{skew})$ 和 $t_{cd} \geq t_{hold} + t_{skew} - t_{ccq}$。

可以看到时钟偏移显著增加了建立时间和保持时间，所以一般不能允许时钟偏移太大。有时甚至可以增大 $t_{ccq}$ 来防止出现问题。

## 亚稳态

如果在孔径时间内改变输入，会导致时序电路进入亚稳态。亚稳态最终会掉落到两个稳态之一，但是掉落到哪个是不确定的，由概率分布函数给出。

# 参考资料

1. *Digital Design and Computer Architecture 2nd*, Chapter 2
2. *Digital Design and Computer Architecture 2nd*, Chapter 3
