---
layout: "post"
title: "「形式语言」01 Grammar"
subtitle: "文法"
author: "roife"
date: 2021-09-22

tags: ["形式语言@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 文法

## 文法

文法（Grammar）是一个四元组：$G = (V, T, P, S)$。

- $V$ 是变量（variable）的非空有穷集。$\forall A \in V$，$A$ 称为变量或非终结符（nonerminal），表示了一个语法范畴（Syntactic Category），记作 $L(A)$
- $T$ 是终结符（terminal）的非空有穷集。$\forall a \in T$，$a$ 是一个终结符。$V \cap U = \emptyset$
- $P$ 是产生式（production）的非空有穷集，规则形式为 $\alpha \rightarrow \beta$，其中 $\alpha \in (V \cup T)^+$，$\beta \in (V \cup T)^*$
- $S$ 是开始符号（start symbol）

## 推导

设 $G = (V, T, P, S)$ 是一个文法，如果 $\alpha \rightarrow \beta \in P$，$\gamma, \delta \in (V \cup T)^*$，则称 $\gamma \alpha \delta \xRightarrow[G]{} \gamma \beta \delta$ 为推导（derivation）。反之称为规约（reduction）。

- $\xRightarrow{+}$，$\xRightarrow{*}$，$\xRightarrow{n}$ 分别表示至少推一步、推若干步和推 $n$ 步

## 语言

设 $G = (V, T, P, S)$，则称 $L(G) = \\{w \vert w \in T^* \operatorname{\mathtt{and}} S \xRightarrow[]{*} w\\}$ 是文法的语言（language）。$\forall w \in L(G)$，$w$ 是 $G$ 的一个句子（sentence）。

## 句型

设 $G = (V, T, P, S)$，则 $\forall \alpha \in (V \cup T)^\ast$ ，如果 $S \xRightarrow[]{*} \alpha$，则称 $\alpha$ 是 $G$ 产生的一个句型（sentence form）。

句子和句型的区别在于是否**可能**包含非终结符。

# Chomosky 体系

- 0 型文法是等价的
- 1 型文法：$\forall \alpha \rightarrow \beta \in P, \vert \beta \vert \ge \vert \alpha \vert$
- 2 型文法：$\forall \alpha \rightarrow \beta \in P, \vert \beta \vert \ge \vert \alpha \vert, \alpha \in V$
- 3 型文法：$\forall \alpha \rightarrow \beta \in P$ 都具有以下形式：
  + $A \rightarrow w$ 或 $A \rightarrow w B$（$A, B \in V, w \in T^+$）

4 种文法分别都有对应的名字：

- 0 型: PSG（phrase structure grammar），对应的语言是 PSL
- 1 型: CSG（context sensitive grammar），对应的语言是 CSL
- 2 型: CFG（context free grammar），对应的语言是 CFL
- 3 型: RG（regular grammar），对应的语言是 RL

显然 4 种文法之间存在依次包含的关系。

## 线性文法

- 线性文法（liner grammar）：设 $G = (V, T, P, S)$，如果 $\forall \alpha \rightarrow \beta \in P$ 都具有以下形式：
  + $A \rightarrow w$ 或 $A \rightarrow wB$（$A, B \in V, w \in T^**$），则 $G$ 为线性文法
- 左线性文法（left liner grammar）：$\alpha \rightarrow \beta$ 为 $A \rightarrow w$ 或 $A \rightarrow Bw$
- 右线性文法（right liner grammar）：$\alpha \rightarrow \beta$ 为 $A \rightarrow w$ 或 $A \rightarrow wB$

右线性文法即为 RG。由于左线性文法和右线性文法等价，所以左线性文法也是 RG。但是如果一个语言的规则混合了左右线性文法，则不是 RG。

## 空语句

定义 $A \rightarrow \varepsilon$ 是空语句。

空语句是否存在不影响语言的性质。

# 构造文法

这里选两个比较有意思的文法构造题。

## $\\{a^nb^nc^n | n \ge 1\\}$

$$
S \rightarrow abc | aSBc
$$

$$
cB \rightarrow Bc
$$

$$
bB \rightarrow bb
$$

可以发现构造过程分为三步：
- 首先构造出数量相等的 `aBc`
- 将 `B` 与 `c` 互换
- 将 `B` 转换为 `b`

## $\\{xx | x \in \Sigma^+\\}$

$L(S) = \\{xx \vert x \in \Sigma^+\\}$，下列文法中 $\alpha, \beta \in \\{A, B\\}$：

$$
S \rightarrow D_1 D_2 T E
$$

$$
T \rightarrow \alpha_1 \alpha_2 \{T\}
$$

$$
\alpha_2 \beta_1 \rightarrow \beta_1 \alpha_2
$$

$$
A_2 E \rightarrow Ea \\
B_2 E \rightarrow Eb
$$

$$
D_2 E \rightarrow F
$$

$$
A_1 F \rightarrow Fa \\
B_1 F \rightarrow Fb
$$

$$
D_1 F \rightarrow \varepsilon
$$

构造过程分为步：
- 构造出 $D_1 D_2 \alpha_1 \alpha_2 \beta_1 \beta2 E$
- 使用规则 $\alpha_2 \beta_1 \rightarrow \beta_1 \alpha_2$ 将所有的 $1$ 换到 $2$ 前面（类似于冒泡），同时所有 $1$ 和 $2$ 的相对顺序不变
 + 此时变成 $D_1 \alpha_1 \beta_1 D_2 \alpha_2 \beta_2 E$
- 从后面开始求值（只能从后面开始求值，这里的规则隐含了强制求值顺序）

虽然从文法上看这里是 0 型文法，但是实际上这个是和 1 型文法是等价的。
