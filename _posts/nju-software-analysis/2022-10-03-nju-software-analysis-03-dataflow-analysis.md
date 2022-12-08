---
layout: "post"
title: "「NJU - Software Analysis」 03 Dataflow Analysis"
subtitle: "数据流分析"
author: "roife"
date: 2022-10-03

tags: ["程序分析@Tags", "南大软件分析@课程相关", "课程相关@Tags", "数据流分析@程序分析", "未完成@Tags", "编译@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 数据流分析

- Application-specific Data: abstraction facts
- Nodes: Transfer function
- Edges: Control-flow handling

In each data-flow analysis application, we associate with every program point a data-flow value that represents an **abstraction** of the set of **all possible program states** that can be observed for that point.

Data-flow analysis is to find a solution to a set of **safe-approximation-directed constraints** (based on semantics and control flows) on the IN[s]’s and OUT[s]’s, for all statements s.

- 前向分析：按程序执行顺序的分析 $\operatorname{\mathtt{OUT}}[s]=f_s(\operatorname{\mathtt{IN}}[s])$
- 反向分析：$\operatorname{\mathtt{IN}}[s]=f_s(\operatorname{\mathtt{OUT}}[s])$

# 常见的几种数据流分析

## Reaching Definitions Analysis (May)

- 问题定义：对于变量 $v$ 的某个定义 $d$，是否存在一条从 $p$ 到 $q$ 的路径，使得 $v$ 的定义不变（即始终为 $d$）
- 应用举例：到达定义可以用来检测未定义的变量（在 entry block 里面加一个 dummy def，然后在使用的地方检测这个 def 是否 reach）

每个 def 都可以用 bit vector 表示，这样就可以用位运算来加速算法。

$$
\begin{aligned}
& \operatorname{\mathtt{OUT}}[\operatorname{\mathtt{entry}}] = \emptyset \\
& \operatorname{\mathtt{for}} (\text{each BasicBlock}\ B \backslash \operatorname{\mathtt{entry}}) \\
& \qquad \operatorname{\mathtt{OUT}}[B] = \emptyset \\
& \operatorname{\mathtt{while}} (\operatorname{\mathtt{OUT}} \text{changes}) \\
& \qquad \operatorname{\mathtt{for}} (\text{each BasicBlock}\ B \backslash \operatorname{\mathtt{entry}}) \\
& \qquad \qquad \operatorname{\mathtt{IN}}[B] = \bigcup_{P \in \operatorname{\mathtt{pred}}(B)}  \operatorname{\mathtt{OUT}}[P] \\
& \qquad \qquad \operatorname{\mathtt{OUT}}[B] = \operatorname{\mathtt{gen}}_B \cup (\operatorname{\mathtt{IN}}[B] - \operatorname{\mathtt{kill}}_B)
\end{aligned}
$$

## Liveness Analysis (May)

- 问题定义：对于 $p$ 处的变量 $v$，从 $p$ 开始到 $\operatorname{\mathtt{exit}} 的 CFG 中是否有某条路径用到了 $v$。如果用到了 $v$，则 $v$ 在 $p$ 点为 live，否则为dead。（重定义后算新变量）
- 应用举例：寄存器分配

$$
\begin{aligned}
& \operatorname{\mathtt{IN}}[\operatorname{\mathtt{exit}}] = \emptyset \\
& \operatorname{\mathtt{for}} (\text{each BasicBlock}\ B \backslash \operatorname{\mathtt{exit}}) \\
& \qquad \operatorname{\mathtt{IN}}[B] = \emptyset \\
& \operatorname{\mathtt{while}} (\operatorname{\mathtt{IN}} \text{changes}) \\
& \qquad \operatorname{\mathtt{for}} (\text{each BasicBlock}\ B \backslash \operatorname{\mathtt{exit}}) \\
& \qquad \qquad \operatorname{\mathtt{OUT}}[B] = \bigcup_{P \in \operatorname{\mathtt{pred}}(B)}  \operatorname{\mathtt{IN}}[P] \\
& \qquad \qquad \operatorname{\mathtt{IN}}[B] = \operatorname{\mathtt{use}}_B \cup (\operatorname{\mathtt{OUT}}[B] - \operatorname{\mathtt{def}}_B)
\end{aligned}
$$

注意这里的 $\operatorname{\mathtt{use}}_B 表示在 def 之前的 use。

## Available Expressions Analysis (must analysis)

- 问题定义：程序点 $p$ 处的表达式 $x \operatorname{\mathtt{op}} y$ 满足 2 个条件。一是从 $\operatorname{\mathtt{entry}}$ 到 $p$ 点必经过 $x \operatorname{\mathtt{op}} y$，二是最后一次使用 $x \operatorname{\mathtt{op}} y$ 后，没有重定义操作数 $x, y$
- 应用举例：复写传播/公共子表达式传播

$$
\begin{aligned}
& \operatorname{\mathtt{OUT}}[\operatorname{\mathtt{entry}}] = \emptyset \\
& \operatorname{\mathtt{for}} (\text{each BasicBlock}\ B \backslash \operatorname{\mathtt{entry}}) \\
& \qquad \operatorname{\mathtt{OUT}}[B] = U \\
& \operatorname{\mathtt{while}} (\operatorname{\mathtt{OUT}} \text{changes}) \\
& \qquad \operatorname{\mathtt{for}} (\text{each BasicBlock}\ B \backslash \operatorname{\mathtt{entry}}) \\
& \qquad \qquad \operatorname{\mathtt{IN}}[B] = \bigcap_{P \in \operatorname{\mathtt{pred}}(B)}  \operatorname{\mathtt{OUT}}[P] \\
& \qquad \qquad \operatorname{\mathtt{OUT}}[B] = \operatorname{\mathtt{gen}}_B \cup (\operatorname{\mathtt{IN}}[B] - \operatorname{\mathtt{kill}}_B)
\end{aligned}
$$

注意在开始的时候假设所有表达式都可达。

在 Available expression analysis 中有一种特殊情况，如下图。虽然 $x$ 被重新赋值了，但是这个表达式仍然能继续传播，因为表达式的值虽然变了，但是可以用类似于 Phi 函数等方式来进行传播（即只是传播的变量不一样了）。

![Available expression analysis](/img/in-post/post-nju-software-analysis/available-expression.jpg)

# 数学基础


