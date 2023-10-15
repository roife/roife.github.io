+++
title = "[形式语言] 01 Grammar"
author = ["roife"]
date = 2021-09-22
aliases = ["/posts/2021-09-22-formal-languages-and-automata-01-grammar"]
series = ["formal-language-and-automata"]
tags = ["形式语言"]
draft = false
+++

## 文法 {#文法}


### 文法 {#文法}

<div class="definition">

**(文法)**

**文法**（Grammar）是一个四元组：\\(G = (V, T, P, S)\\)。

-   \\(V\\) 是非**终结符**（nonterminal）的非空有穷集。\\(\forall A \in V\\)，\\(A\\) 表示了一个**语法范畴**（Syntactic Category）
-   \\(T\\) 是**终结符**（terminal）的非空有穷集，\\(V \cap T = \emptyset\\)
-   \\(P\\) 是产生式（production）的非空有穷集
    -   规则形式为 \\(\alpha \rightarrow \beta\\)，其中 \\(\alpha \in (V \cup T)^{+}\\)，\\(\beta \in (V \cup T)^{\*}\\)
-   \\(S\\) 是开始符号（start symbol），\\(S \in V\\)

</div>


### 推导 {#推导}

<div class="definition">

**(推导与规约)**

设 \\(G = (V, T, P, S)\\) 是一个文法，如果 \\(\alpha \rightarrow \beta \in P\\)，\\(\gamma, \delta \in (V \cup T)^\*\\)，则称 \\(\gamma \alpha \delta \xRightarrow[G]{} \gamma \beta \delta\\) 为**推导**（derivation）。反之称为**规约**（reduction）。

</div>

\\(\xRightarrow{+}\\)，\\(\xRightarrow{\*}\\)，\\(\xRightarrow{n}\\) 分别表示至少推一步、推若干步和推 \\(n\\) 步


### 语言 {#语言}

<div class="definition">

**(语言)**

设 \\(G = (V, T, P, S)\\)，则称 \\(L(G) = \\{w \vert w \in T^ \* \wedge S \xRightarrow{\* } w\\}\\) 是文法的**语言**（language）。

</div>

<div class="definition">

**(句子)**

设 \\(G\\) 是文法，\\(\forall w \in L(G)\\)，\\(w\\) 是 \\(G\\) 的一个**句子**（sentence）。

</div>


### 句型 {#句型}

<div class="definition">

**(句型)**

设 \\(G = (V, T, P, S)\\)，则 \\(\forall \alpha \in (V \cup T)^\ast\\) ，如果 \\(S \xRightarrow{\*} \alpha\\)，则称 \\(\alpha\\) 是 \\(G\\) 产生的一个**句型**（sentence form）。

</div>

句子和句型的区别在于是否**可能**包含非终结符。


## Chomosky 体系 {#chomosky-体系}


### 文法 {#文法}

Chomosky 文法体系中分为四级文法：

-   0 型文法（phrase structure grammar, PSG）
-   1 型文法（context sensitive grammar, CSG）：\\(\forall \alpha \rightarrow \beta \in P, \vert \beta \vert \ge \vert \alpha \vert\\)
-   2 型文法（context free grammar, CFG）：\\(\forall \alpha \rightarrow \beta \in P, \vert \beta \vert \ge \vert \alpha \vert, \alpha \in V\\)
-   3 型文法（regular grammar, RG）：\\(\forall \alpha \rightarrow \beta \in P\\) 都具有以下形式：
    -   \\(A \rightarrow w\\) 或 \\(A \rightarrow w B\\)（\\(A, B \in V, w \in T^+\\)）

显然 4 种文法之间存在依次包含的关系。


### 1' 型文法 {#1-型文法}

1' 型文法的定义是 \\(P = \\{\alpha\_{1}A\alpha\_{2} \rightarrow \alpha\_1 \beta \alpha\_2\\}\\)，其中 \\(A \in V. \alpha\_1, \alpha\_2 \in (V \cup T)^\*. \beta \in (V \cup T)^+.\\)

可以证明 1 型文法和 1' 型文法等价。

<div class="proof">

显然，1' 型文法 \\(\subseteq\\) 1 型文法，因此下面只要证明对于任意 1 型文法 \\(G = (V, T, P, S)\\)，存在 1' 型文法 \\(G'\\) 使得 \\(L(G) = L(G')\\)。

令 \\(G' = (V', T, P', S)\\)，其中：

-   \\(V' = V \cup M, M = \\{[a] | a \in T\\}\\)
-   \\(P' = P'' \cup \\{[a] \rightarrow a\\}\\)，其中 \\(P''\\) 是将 \\(P\\) 中的所有 \\(a (a \in T)\\) 替换成 \\([a]\\)

此时 \\(G''\\) 中的产生式有两种情况：

-   \\(A \rightarrow \beta\\)，即 \\(\alpha\_1 = \alpha\_2 = \varepsilon\\)，满足条件
-   \\(A\_1 A\_2 \dots A\_n \rightarrow B\_1 B\_2 B\_3 \dots B\_m\\)，其中 \\(m \ge n \ge 2\\)

将第二种文法替换成下面的形式：

\begin{aligned}
A\_1 A\_2 \dots A\_n &\rightarrow C\_1 A\_2 \dots A\_n \\\\
C\_1 A\_2 \dots A\_n &\rightarrow C\_1 C\_2 \dots A\_n \\\\
&\dots \\\\
C\_1 C\_2 \dots A\_n &\rightarrow C\_1 C\_2 \dots C\_n \\\\
C\_1 C\_2 \dots C\_n &\rightarrow B\_1 C\_2 \dots C\_n \\\\
&\dots \\\\
B\_1 B\_2 \dots C\_{n-1} C\_n &\rightarrow B\_1 B\_2 \dots B\_{n-1} C\_n \\\\
B\_1 B\_2 \dots B\_{n-1} C\_n &\rightarrow B\_1 B\_2 \dots B\_{n-1} B\_n \dots B\_{m}
\end{aligned}

这个替换的第一部分用于逐步将 \\(A\_i\\) 替换成 \\(C\_i\\)，通过 \\(C\_i\\) 的数量来控制产生式的执行次序，并通过 \\(C\_n\\) 来产生多余的 \\(B\_j\\)。

</div>


### 线性文法 {#线性文法}

<div class="definition">

**(线性文法)**

-   **线性文法**（liner grammar）：设 \\(G = (V, T, P, S)\\)，如果 \\(\forall \alpha \rightarrow \beta \in P\\) 都具有以下形式：
    -   \\(A \rightarrow w\\) 或 \\(A \rightarrow wB\\)（\\(A, B \in V, w \in T^\*\*\\)），则 \\(G\\) 为线性文法
-   **左线性文法**（left liner grammar）：\\(\alpha \rightarrow \beta\\) 为 \\(A \rightarrow w\\) 或 \\(A \rightarrow Bw\\)
-   **右线性文法**（right liner grammar）：\\(\alpha \rightarrow \beta\\) 为 \\(A \rightarrow w\\) 或 \\(A \rightarrow wB\\)

</div>

右线性文法即为 RG。由于左线性文法和右线性文法等价，所以左线性文法也是 RG。但是如果一个语言的规则混合了左右线性文法，则不是 RG。


### 空语句 {#空语句}

定义 \\(A \rightarrow \varepsilon\\) 是空语句。

<div class="theorem">

设文法 \\(G = (V, T, P, S)\\)，则存在同类型文法 \\(G' = (V', T, P', S')\\) 使得 \\(L(G) = L(G')\\) 且 \\(S'\\) 不出现在 \\(P'\\) 中任何产生式的右部。

</div>

<div class="proof">

当 G 满足要求时，\\(G' = G\\) 即为所求，否则存在 \\(A \rightarrow xSy \in P\\)。

令 \\(G' = (V \cup \\{S'\\}, T, P', S')\\)，其中 \\(P' = P \cup \\{S' \rightarrow \alpha | S \rightarrow \alpha \in P \\}\\)。添加的产生式并不改变语言的性质。

-   首先证明 \\(L(G) \subseteq L(G')\\)。

    对于 \\(G\\) 中任意推导 \\(S \Rightarrow \alpha \xRightarrow{\*} x\\)，则 \\(G'\\) 中有 \\(S' \Rightarrow \alpha \xRightarrow{ \*} x\\)，因此 \\(L(G) \subseteq L(G')\\)。

-   然后证明 \\(L(G') \subseteq L(G)\\)

    对于 \\(G'\\) 中任意推导 \\(S' \Rightarrow \alpha \xRightarrow{\*} x\\)，由于 \\(S'\\) 不出现在任何产生式的右部，因此 \\(\alpha \Rightarrow{ \*} x\\) 中所使用的产生式皆在 \\(P\\) 中。又由于 \\(S \Rightarrow \alpha \in P\\)，因此 \\(S \Rightarrow \alpha \xRightarrow{ \*} x\\) 成立，即 \\(L(G') \subseteq L(G)\\)。

综上，原命题成立。

</div>

<div class="theorem">

空语句是否存在不影响语言的性质。

</div>

<div class="proof">

设语言 \\(L\\) 对应的文法为 \\(G = (V, T, P, S)\\)。

如果 \\(\varepsilon \notin L\\)，则取 \\(G' = (V, T, P \cup \\{S \rightarrow \varepsilon\\}, S)\\)，添加的规则并不改变语言的性质。不妨设 \\(S\\) 不出现在任何产生式的右部，则 \\(S \rightarrow \varepsilon\\) 不可能出现在非 \\(\varepsilon\\) 的句子推导中，即 \\(L(G) \subseteq L(G')\\)，因此 \\(L(G') = L(G) \cup \\{\varepsilon\\}\\)。

反之类似易证 \\(L(G) - \\{\varepsilon\\}\\) 也不改变语言的性质。

</div>


## 文法构造题 {#文法构造题}

这里选两个比较有意思的文法构造题。


### \\(\\\{a^nb^nc^n | n \ge 1\\\}\\) {#a-nb-nc-n-n-ge-1}

\\[
S \rightarrow abc | aSBc
\\]

\\[
cB \rightarrow Bc
\\]

\\[
bB \rightarrow bb
\\]

可以发现构造过程分为三步：

-   首先构造出数量相等的 `aBc`
-   将 `B` 与 `c` 互换
-   将 `B` 转换为 `b`


### \\(\\\{xx | x \in \Sigma^+\\\}\\) {#xx-x-in-sigma-plus}

\\(L(S) = \\\{xx \vert x \in \Sigma^+\\\}\\)，下列文法中 \\(\alpha, \beta \in \\\{A, B\\\}\\)：

\\[
S \rightarrow D\_1 D\_2 T E
\\]

\\[
T \rightarrow \alpha\_1 \alpha\_2 \\{T\\}
\\]

\\[
\alpha\_2 \beta\_1 \rightarrow \beta\_1 \alpha\_2
\\]

\\[
A\_2 E \rightarrow Ea \\\\
B\_2 E \rightarrow Eb
\\]

\\[
D\_2 E \rightarrow F
\\]

\\[
A\_1 F \rightarrow Fa \\\\
B\_1 F \rightarrow Fb
\\]

\\[
D\_1 F \rightarrow \varepsilon
\\]

构造过程分为三步：

-   构造出 \\(D\_1 D\_2 \alpha\_1 \alpha\_2 \beta\_1 \beta2 E\\)
-   使用规则 \\(\alpha\_2 \beta\_1 \rightarrow \beta\_1 \alpha\_2\\) 将所有的 \\(1\\) 换到 \\(2\\) 前面（类似于冒泡），同时所有 \\(1\\) 和 \\(2\\) 的相对顺序不变
    -   此时变成 \\(D\_1 \alpha\_1 \beta\_1 D\_2 \alpha\_2 \beta\_2 E\\)
-   从后面开始求值（只能从后面开始求值，这里的规则隐含了强制求值顺序）

虽然从文法上看这里是 0 型语言，但是实际上这是个 1 型语言。
