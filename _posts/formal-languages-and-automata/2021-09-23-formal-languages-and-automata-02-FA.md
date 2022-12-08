---
layout: "post"
title: "「形式语言」02 FA"
subtitle: "有穷自动机"
author: "roife"
date: 2021-09-23

tags: ["形式语言@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# FA

有穷状态自动机（finite automata，FA）

$$M = (Q, \Sigma, \delta, q_0, F)$$

- $Q$：状态（state）的非空有穷集合
- $\Sigma$：输入字母表（input alphabet）
- $\delta$：状态转移函数（transition function）。$\delta : Q \times \Sigma \rightarrow Q$
  + $\forall (q, a) \in Q \times \Sigma, \delta(q, a) = p$ 表示 $M$ 在状态 $q$ 下读入字符 $a$，则将状态转移到 $p$ 并将读头指向下一个字符串
- $q_0$：开始状态（initial state）。$q_0 \in Q$
- $F$：终止状态（final state）或接受状态（accept state）

用于识别语言时可以用 $\hat{\delta} : Q \times \Sigma^* \rightarrow Q$（后面的 $\delta$ 都是指 $\hat{\delta}$）：
- $\hat{\delta}(q, \varepsilon) = q$
- $\hat{\delta}(q, wa) = \delta(\hat{\delta}(q, w), a)$

## 接受

设 $M = (Q, \Sigma, \delta, q_0, F)$，对于 $\forall x \in \Sigma^*$，如果 $\delta(q_0, x) \in F$，则称 $x$ 被 $M$ 接受。

$$
L(M) = \{x | x \in \Sigma^x \operatorname{\mathtt{and}} \delta(q_0, x) \in F\}
$$

如果 $L(M_1) = L(M_2)$ 则两个 FA 等价。

## 即时描述

设 $M = (Q, \Sigma, \delta, q_0, F)$，$x, y \in \Sigma^*$，$\delta(q_0, x) = q$，则 $xqy$ 称为 $M$ 的一个即时描述（instantaneous description, ID），记作

$$
xq_0ay \vdash_M xayqb
$$

# DFA 上的接受定义

如果 $\forall q \in Q, a \in \Sigma$，$\delta(q, a)$ 都有确定的值，则称之为有穷状态自动机（deterministic finite automaton，DFA）。

## DFA 上的等价类划分

定义 $\operatorname{\mathtt{set}}(q) = \\{ x \vert x \in \Sigma^*, \delta(q_0, x) = q\\}$。

在 DFA 上定义关系 $R_M$ 为 $\forall x, y \in \Sigma^*, x R_M y \Leftrightarrow \exists q \in Q, x \in \operatorname{\mathtt{set}}(q) \operatorname{\mathtt{and}} y \in \operatorname{\mathtt{set}}(q)$。

可以发现，$R_M$ 定义了 $\Sigma^*$ 上面的一个等价类。即 DFA 上面的每个状态都对应了 $\Sigma^*$ 的一个划分。

反过来，如果某个语言能划分成有限个等价类，那么就可以考虑用 DFA 描述。

# NFA

非确定性有穷状态自动机（non-deterministic finite automaton，NFA）

$$M =(Q, \Sigma, \delta, q_0, F)$$

- $Q, \Sigma, q_0, F$ 的意义与 DFA 相同
- $\delta: Q \times \Sigma \rightarrow 2^Q$
  + $\forall (q, a) \in Q \times \Sigma, \delta(q, s) = \\{p_1, p_2, \cdots p_m\\}$ 表示 $M$ 在状态 $q$ 下读入字符 $a$，则将状态转移到 $p_i$ 并将读头指向下一个字符串

同样 $\hat{\delta}$ 的定义也需要扩充：$\hat{\delta} : Q \times \Sigma^* \rightarrow 2^Q, q \in Q, w \in \Sigma^*, a \in \Sigma$
- $\hat{\delta}(q, \varepsilon) = \\{q\\}$
- $\hat{\delta}(q, wa) = \\{p \vert \exists r \in \hat{\delta}(q, w) \operatorname{\mathtt{where}} p \in \delta(r, a) \\}$

NFA 与 DFA 的区别在于，输入同一个字符可以有多个不同的转移路径。NFA 将 DFA 中的“值”变成了“集合”，此时可以看作是“拥有智能的”DFA，可以自动选择路径。

## NFA 上的接受定义

设 $M = (Q, \Sigma, \delta, q_0, F)$，对于 $\forall x \in \Sigma^*$，如果 $\delta(q_0, x) \cap F \ne \emptyset$，则称 $x$ 被 $M$ 接受。

$$
L(M) = \{x | x \in \Sigma^x \operatorname{\mathtt{and}} \delta(q_0, x) \cap F \ne \emptyset\}
$$

## DFA 与 NFA 等价

- 给定任意的 DFA，都存在一个 NFA 与之对应。（显然，因为 DFA 就是 NFA 的一种）
- 给定任意的 NFA，都存在一个 DFA 与之对应。（构造）

给定一个 NFA $M_1 = (Q_1, \Sigma, \delta_1, q_0, F_1)$，下面要构造 DFA $M_2 = (Q_2, \Sigma, \delta_2, [q_0], F_2)$。其中 $Q_2 = 2^{Q_1}$。

$[q_1, q_2, \dots, q_n]$ 表示一个综合状态，对应了当前同时处于 NFA 上的 $q_1, q_2, \dots, q_n$ 状态。也就是说 DFA 上用一个状态，表示了在 NFA 上“同时处于多个点”的状态，所以 DFA 有 $2^n$ 个点。

设在 NFA 上有 $\delta_1(\\{q_1, q_2, \dots, q_n\\}, a) = \\{p_1, p_2, \dots, p_m\\}$，则在 DFA 上对应建立转移 $\delta_1([q_1, q_2, \dots, q_n], a) = [p_1, p_2, \dots, p_m]$。

当有些状态构造出来可能实际上无法从初始状态转移过来时，这些状态可以被删掉。

可以证明这样的 DFA 与 NFA 等价。

# $\varepsilon$-NFA

带空转移的非确定性有穷状态自动机（non-deterministic finite automaton with $\varepsilon$ moves，$\varepsilon$-NFA）

$$M =(Q, \Sigma, \delta, q_0, F)$$

- $Q, \Sigma, q_0, F$ 的意义与 DFA 相同
- $\delta: Q \times (\Sigma \cup \\{ \varepsilon \\}) \rightarrow 2^Q$
  + 对于 $\forall (q, a) \in Q \times \Sigma, \delta(q, s) = \\{p_1, p_2, \cdots p_m\\}$ 表示 $M$ 在状态 $q$ 下读入字符 $a$，则可以将状态转移到 $p_i$ 并将读头指向下一个字符串
  + 对于 $\forall q \in Q, \delta(q, \varepsilon) = \\{p_1, p_2, \cdots p_m\\}$ 表示 $M$ 在状态 $q$ 下不读入字符，并将状态转移到 $p_i$ 并将读头指向下一个字符串

同样 $\hat{\delta}$ 的定义也需要扩充：$\hat{\delta} : Q \times \Sigma^* \rightarrow 2^Q, P \subseteq Q, q \in Q, w \in \Sigma^*, a \in \Sigma$
- $\varepsilon-CLOSURE(q) = \\{p \vert q \overset{\varepsilon}{\rightarrow} p \\}$
- $\varepsilon-CLOSURE(P) = \bigcup_{p \in P} \varepsilon-CLOSURE(p)$
- $\hat{\delta}(q, \varepsilon) = \varepsilon-CLOSURE(q)$
- $\hat{\delta}(q, wa) = \varepsilon-CLOSURE(P)$

$$
\begin{aligned}
P &= \{p \vert \exists r \in \hat{\delta}(q, w)\ \operatorname{\mathtt{where}}\ p \in \delta(r, a)\} \\
&= \bigcup_{r \in \hat{\delta}(q, w)} \delta(r, a)
\end{aligned}
$$

进一步扩展：
- $\delta : 2^Q \times \Sigma \rightarrow 2^Q$，$\forall (P, a) \in 2^Q \times \Sigma$，则 $\delta(P, a) = \bigcup_{q \in P} \delta(q, a)$
- $\hat{\delta} : 2^Q \times \Sigma^\ast \rightarrow 2^Q$，$\forall (P, w) \in 2^Q \times \Sigma^\ast$，则 $\hat{\delta}(P, a) = \bigcup_{q \in P} \hat{\delta}(q, w)$

注意，在 $\varepsilon$-NFA 中，$\hat{\delta} \noteq \delta$。

## $\varepsilon$-NFA 上的接受定义

设 $M = (Q, \Sigma, \delta, q_0, F)$，对于 $\forall x \in \Sigma^*$，如果 $\hat{\delta}(q_0, x) \cap F \ne \emptyset$，则称 $x$ 被 $M$ 接受。

$$
L(M) = \{x | x \in \Sigma^x \operatorname{\mathtt{and}} \hat{\delta}(q_0, x) \cap F \ne \emptyset\}
$$

## NFA 与 $\varepsilon$-NFA 等价

- 给定任意的 NFA，都存在一个 $\varepsilon$-NFA 与之对应。（显然）
- 给定任意的 $\varepsilon$-NFA，都存在一个 NFA 与之对应。（构造）

给定一个 $\varepsilon$-NFA $M_1 = (Q, \Sigma, \delta_1, q_0, F_1)$，下面要构造 DFA $M_2 = (Q, \Sigma, \delta_2, q_0, F_2)$。

$$
\delta_2(q, a) = \hat{\delta}_1(q, a)
$$

$$
F_2 =
\begin{cases}
F \cup \{q_0\} & \text{if}\ F \cap \varepsilon-CLOSURE(q_0) \ne \emptyset \\
F & \text{if}\ F \cap \varepsilon-CLOSURE(q_0) = \emptyset
\end{cases}
$$
