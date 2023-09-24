+++
title = "[形式语言] 02 Finite automata"
author = ["roife"]
date = 2021-09-23
aliases = ["/posts/2021-09-23-formal-languages-and-automata-02-finite-automata"]
series = ["formal-language-and-automata"]
tags = ["形式语言"]
draft = false
+++

## DFA {#dfa}


### 定义 {#定义}

<div class="definition">

**(DFA)**

**确定性有穷状态自动机**（Deterministic finite automata，DFA）是一个五元组：

\\[M = (Q, \Sigma, \delta, q\_0, F)\\]

-   \\(Q\\)：状态（state）的非空有穷集合
-   \\(\Sigma\\)：输入字母表（input alphabet）
-   \\(\delta\\)：状态转移函数（transition function）
    -   \\(\delta : Q \times \Sigma \rightarrow Q\\)
    -   \\(\delta(q, a) = p\\) 表示 \\(M\\) 在状态 \\(q\\) 下读入字符 \\(a\\)，则将状态转移到 \\(p\\) 并将读头指向下一字符串
-   \\(q\_0\\)：开始状态（initial state），\\(q\_0 \in Q\\)
-   \\(F\\)：终止状态（final state）或接受状态（accept state），\\(F \subseteq Q\\)

</div>

用于识别语言时可以用 \\(\hat{\delta} : Q \times \Sigma^\* \rightarrow Q\\)（为了方便起见，后面的 \\(\delta\\) 都是指 \\(\hat{\delta}\\)）：

\\[\hat{\delta}(q, x) =
\begin{cases}
q, & x = \varepsilon \\\\
\delta(\hat{\delta}(q, w), a), & x = wa\\\\
\end{cases}\\]

DFA 可以看成具有有穷的存储功能。


### 接受 {#接受}

<div class="definition">

**(DFA 接受)**

设 \\(M = (Q, \Sigma, \delta, q\_0, F)\\)，对于 \\(\forall x \in \Sigma^\*\\)，如果 \\(\delta(q\_0, x) \in F\\)，则称 \\(x\\) 被 \\(M\\) 接受。

\\[
L(M) = \\{x | \delta(q\_0, x) \in F\\}
\\]

</div>

如果 \\(L(M\_1) = L(M\_2)\\) 则两个 FA **等价**。


### 即时描述 {#即时描述}

<div class="definition">

**(即时描述)**

设 \\(M = (Q, \Sigma, \delta, q\_0, F)\\)，\\(x, y \in \Sigma^\*\\)，\\(\delta(q\_0, x) = q\\)，则 \\(xqy\\) 称为 \\(M\\) 的一个即时描述（instantaneous description, ID），记作

\\[
xq\_0ay \vdash\_M xayqb
\\]

</div>


### 陷阱状态 {#陷阱状态}

DFA 中缺少的边（状态转移）都默认转移到一个**陷阱状态**（trap）中。陷阱状态只有入边，没有出边，因此 FA 会在这个陷阱状态中读完剩下的字母，并且不会接受这个字符串。

一般可以省略图中的陷阱状态。


## NFA {#nfa}


### 定义 {#定义}

<div class="definition">

**(NFA)**

\*非确定性有穷状态自动机\*（non-deterministic finite automaton，NFA）

\\[M =(Q, \Sigma, \delta, q\_0, F)\\]

-   \\(Q, \Sigma, q\_0, F\\) 的意义与 DFA 相同
-   \\(\delta: Q \times \Sigma \rightarrow 2^Q\\)
    -   \\(\delta(q, a) = \\{p\_1, p\_2, \cdots p\_m\\} | p\_i \subseteq Q\\) 表示 \\(M\\) 在状态 \\(q\\) 下读入字符 \\(a\\)，可以将状态转移到 \\(p\_i\\) 并指向下一个字符

</div>

同样 \\(\hat{\delta}\\) 的定义也需要扩充：\\(\hat{\delta} : Q \times \Sigma^\* \rightarrow 2^Q\\)

\\[\hat{\delta}(q, x) =
\begin{cases}
\\{q\\}, & x = \varepsilon \\\\
\bigcup\_{p \in \hat{\delta}(q, w)}\delta(p, a), &x = wa
\end{cases}\\]

NFA 与 DFA 的区别在于，输入同一个字符可以有多个不同的转移路径。NFA 将 DFA 中的“值”变成了“集合”，此时可以看作是“拥有智能的”DFA，可以自动选择路径。


### NFA 上的接受定义 {#nfa-上的接受定义}

<div class="definition">

**(NFA 接受)**

设 \\(M = (Q, \Sigma, \delta, q\_0, F)\\)，对于 \\(\forall x \in \Sigma^\*\\)，如果 \\(\delta(q\_0, x) \cap F \ne \emptyset\\)，则称 \\(x\\) 被 \\(M\\) 接受。

\\[
L(M) = \\{x | \delta(q\_0, x) \cap F \ne \emptyset\\}
\\]

</div>


### DFA 与 NFA 等价 {#dfa-与-nfa-等价}

<div class="theorem">

DFA 与 NFA 等价

</div>

<div class="proof">

首先，显然 DFA \\(\subseteq\\) NFA，下面只要证明 NFA \\(\subseteq\\) DFA。这个证明称为子集构造法。

给定一个 NFA \\(M\_1 = (Q\_1, \Sigma, \delta\_1, q\_0, F\_1)\\)，下面要构造 DFA \\(M\_2 = (Q\_2, \Sigma, \delta\_2, [q\_0], F\_2)\\)。其中 \\(Q\_2 = 2^{Q\_1}\\)。

令 \\([q\_1, q\_2, \dots, q\_n]\\) 表示一个 \\(Q\_1\\) 中的子集，对应了当前同时处于 NFA 上的 \\(q\_1, q\_2, \dots, q\_n\\) 状态。设在 NFA 上有 \\(\delta\_1(\\{q\_1, q\_2, \dots, q\_n\\}, a) = \bigcup\_{i=1}^{n}\delta(q\_i, a) = \\{p\_1, p\_2, \dots, p\_m\\}\\)，则在 DFA 上对应建立转移 \\(\delta\_2([q\_1, q\_2, \dots, q\_n], a) = [p\_1, p\_2, \dots, p\_m]\\)。

接收状态集合 \\(F\_2 = \\{[P \subseteq 2^{Q\_1}] | F \cap P \ne \emptyset\\}\\)。

当有些状态构造出来可能实际上无法从初始状态转移过来时，这些状态可以被删掉。

下面通过归纳 \\(|w|\\) 证明 \\(M\_1 = M\_2\\)：

-   基础情况：\\(w = \varepsilon\\)，显然成立
-   归纳：设 \\(w = xa\\)，则
    -   \\(\delta\_1(q\_0, xa) = \bigcup\_{p \in \delta\_1(q\_0, x)}\delta\_1(p, a)\\)
    -   \\(\delta\_2([q\_0], w) = \bigcup\_{p \in \delta\_2([q\_0], x)}\delta\_2(p, a)\\)
    -   由归纳假设知 \\(\delta\_1(q\_0, x) = \delta\_2([q\_0], x)\\)，且 \\(\forall p \in V, a \in T. \delta\_1(p, a) = \delta\_2([p], a)\\)

</div>

在这个构造中用 DFA 的一个点，表示了在 NFA 上“同时处于多个点”的状态，所以 DFA 至多有 \\(2^n\\) 个点。这个方法的巧妙之处在于尽管 NFA 是不确定性的，但是 NFA 的状态空间是有限的，因此可以用 DFA 构造出 NFA 的所有状态。


## \\(\varepsilon\\)-NFA {#varepsilon-nfa}


### 定义 {#定义}

<div class="definition">

**(\\(\varepsilon\\)-NFA)**

**带空转移的非确定性有穷状态自动机**（non-deterministic finite automaton with \\(\varepsilon\\) moves，\\(\varepsilon\\)-NFA）

\\[M =(Q, \Sigma, \delta, q\_0, F)\\]

-   \\(Q, \Sigma, q\_0, F\\) 的意义与 DFA 相同
-   \\(\delta: Q \times (\Sigma \cup \\{ \varepsilon \\}) \rightarrow 2^Q\\)
    -   对于 \\(\delta(q, s) = \\{p\_1, p\_2, \cdots p\_m\\}\\) 表示 \\(M\\) 在状态 \\(q\\) 下读入字符 \\(a\\)，则可以将状态转移到 \\(p\_i\\) 并将读头指向下一个字符
    -   对于 \\(\delta(q, \varepsilon) = \\{p\_1, p\_2, \cdots p\_m\\}\\) 表示 \\(M\\) 在状态 \\(q\\) 下不读入字符，并将状态转移到 \\(p\_i\\)

</div>

同样 \\(\hat{\delta}\\) 的定义也需要扩充：\\(\hat{\delta} : Q \times \Sigma^\* \rightarrow 2^Q, P \subseteq Q, q \in Q, w \in \Sigma^\*, a \in \Sigma\\)

<div class="definition">

**(闭包)**

状态集合 \\(P\\) 的闭包定义如下：

\\[\varepsilon-CL(P)=
\begin{cases}
\\{q \vert p \overset{\varepsilon}{\rightarrow} q \in \delta \\}, &P = \\{p\\} \\\\
\bigcup\_{p \in P} \varepsilon-CL(p), &\text{else}
\end{cases}\\]

当然 \\(\delta(q, \varepsilon) = q\\)

</div>

则

\\[\hat{\delta}(q, x) =
\begin{cases}
\varepsilon-CL(q), & x = \varepsilon \\\\
\bigcup\_{p \in \hat{\delta}(q, w)}\varepsilon-CL(\delta(p, a)), &x = wa
\end{cases}\\]

注意在这里 \\(\delta(q, \varepsilon) \ne \hat{\delta}(q, \varepsilon)\\)。


### \\(\varepsilon\\)-NFA 上的接受定义 {#varepsilon-nfa-上的接受定义}

<div class="definition">

**(\\(\varepsilon\\)-NFA 的接受)**

设 \\(M = (Q, \Sigma, \delta, q\_0, F)\\)，对于 \\(\forall x \in \Sigma^\*\\)，如果 \\(\hat{\delta}(q\_0, x) \cap F \ne \emptyset\\)，则称 \\(x\\) 被 \\(M\\) 接受。

\\[
L(M) = \\{x | \hat{\delta}(q\_0, x) \cap F \ne \emptyset\\}
\\]

</div>


### NFA 与 \\(\varepsilon\\)-NFA 等价 {#nfa-与-varepsilon-nfa-等价}

<div class="theorem">

NFA 与 \\(\varepsilon\\)-NFA 等价。

</div>

<div class="proof">

给定一个 \\(\varepsilon\\)-NFA \\(M\_1 = (Q, \Sigma, \delta\_1, q\_0, F\_1)\\)，下面要构造 NFA \\(M\_2 = (Q, \Sigma, \delta\_2, q\_0, F\_2)\\)。

其中

\\[
\delta\_2(q, a) = \hat{\delta}\_1(q, a)
\\]

\\[F\_2 = \\{q | \varepsilon-CL(q) \cap F\_1 \ne \emptyset\\}\\]

等价性可以通过归纳证明。

</div>

由上可知 DFA，NFA，\\(\varepsilon\\)-NFA 三者两两等价。


## 正则语言与 FA {#正则语言与-fa}


### RL 与 FA 等价 {#rl-与-fa-等价}

<div class="theorem">

RL 与 FA 等价。

</div>

<div class="proof">

只要证明 RL \\(\subseteq\\) FA，且 FA \\(\subseteq\\) RL 即可。

-   首先证明 FA 能够接受 RL。需要对于任意 RL，要构造一个与之等价的 FA。对于正则文法 \\(G = (V, T, P, S)\\)，构造 \\(M = (V \cup \\{Z\\}, T, \delta, S, \\{Z\\})\\)，其中 \\(\delta\\) 的定义如下：

    \\[\delta(A, a) =
      \begin{cases}
      \\{B | A \rightarrow aB \in P\\} \cup \\{Z\\}, & A \rightarrow a \in P \\\\
      \\{B | A \rightarrow aB \in P\\} , & A \rightarrow a \notin P
      \end{cases}\\]

    下面证明 \\(L(M) = L(G)\\)。设 \\(a\_1 a\_2 \dots a\_n \in L(G)\\)，即有推导

    \begin{aligned}
      & S \xRightarrow{+} a\_1 a\_2 \dots a\_n \\\\
    \Leftrightarrow& S \Rightarrow a\_1 A\_1 \Rightarrow a\_1 a\_2 A\_2 \Rightarrow \dots \Rightarrow a\_1 a\_2 \dots a\_n
    \end{aligned}

    因此

    \begin{aligned}
    & S \rightarrow a\_1 A\_1 \in P \\\\
    & A\_1 \rightarrow a\_2 A\_2 \in P \\\\
    & \dots \\\\
    & A\_{n-2} \rightarrow a\_{n-1} A\_{n-1} \in P \\\\
    & A\_{n-1} \rightarrow a\_n \in P
    \end{aligned}

    根据此文法，对于 \\(\delta\\) 有

    \begin{aligned}
    & A\_1 \in \delta(S, a\_1) \\\\
    & A\_2 \in \delta(A\_1, a\_2) \\\\
    & \dots \\\\
    & A\_{n-1} \in \delta(A\_{n-2}, a\_{n-1}) \\\\
    & Z \in \delta(A\_{n-1}, a\_n)
    \end{aligned}

    因此 \\(Z \in \delta(S, a\_1 a\_2 \dots a\_n)\\)，成立。

    这里需要特殊处理 \\(\varepsilon\\) 的情况。不妨假设 \\(S\\) 不出现在任何产生式的右部。设 \\(S \rightarrow \varepsilon \in P\\)，则定义转移 \\(\delta(S, \varepsilon) = \\{Z\\}\\)，由于 \\(S\\) 不出现在产生式的右部，因此 FA 上的转移无法回到 \\(S\\)，即这个转移不会对其他句子的接受产生影响。

-   下面证明 FA 接受的句子都是 RL。由于三种 FA 等价，因此这里只需要证明 DFA 接受的句子是 RL。设 DFA \\(M = (Q, \Sigma, \delta, q\_0, F)\\)，构造 \\(G = (Q, \Sigma, P, q\_0)\\)，其中

    \\[P = \\{ q \rightarrow a p | \delta(q, a) = p \\} \cup \\{q \rightarrow a | \delta(q, a) = p \in F \\}\\]

    证明类似。同样这里需要考虑 \\(\varepsilon\\) 相关的句子。假设 \\(q\_0 \notin F\\)，则 \\(\varepsilon \notin L(M)\\)，不影响。如果 \\(q\_0 \in F\\)，由于空句子存在与否不影响语言性质，因此存在正则文法 \\(G'\\) 使得 \\(L(G') = L(G) \cup \\{\varepsilon\\} = L(M)\\)。

综上，命题成立。

</div>


### 左线性文法与 FA 等价 {#左线性文法与-fa-等价}

类似 RL 与 FA 等价的证明。只不过 RL 中证明利用了“推导”的顺序，而左线性文法的证明利用了“规约”的顺序。

<div class="theorem">

左线性文法的语言与 FA 等价。

</div>

<div class="proof">

-   首先证明 FA 能够接受左线性文法的语言。对于左线性文法 \\(G = (V, T, P, Z)\\)，构造 \\(M = (V \cup \\{S\\}, T, \delta, S, \\{Z\\})\\)，其中 \\(\delta\\) 的定义如下：

    \\[\delta(B, a) = \begin{cases}
      \\{A | A \rightarrow a \in P\\} , & B = S \\\\
      \\{A | A \rightarrow Ba \in P\\} , & B \ne S
      \end{cases}\\]

    利用规约可以证明。
-   然后证明 FA 接受的语言可以用左线性文法描述。对于 DFA \\(M = (Q, \Sigma, \delta, q\_0, F)\\)，构造 \\(G = (Q, \Sigma, P, q\_z)\\)，其中

    \\[P = \\{ p \rightarrow q a | \delta(q, a) = p \\} \cup \\{p \rightarrow a | \delta(q\_0, a) = p \\} \cup \\{q\_z \rightarrow q a | \delta(q, a) = p \in F \\} \\]

</div>


### 左右线性文法等价 {#左右线性文法等价}

<div class="theorem">

左右线性文法等价

</div>

<div class="proof">

由于二者皆与 FA 等价，因此二者等价。

</div>


## FA 的变形 {#fa-的变形}


### 双向 FA {#双向-fa}

<div class="definition">

**(2DFA)**

**确定性双向有穷状态自动机**（two-way deterministic finite automation, 2DFA）是一个八元组

\\[M = (Q, \Sigma, \vdash, \dashv, \delta, q\_0, t, r)\\]

-   其中 \\(Q, \Sigma, q\_0, F\\) 的意义同 DFA。
-   \\(\vdash, \dashv\\) 分别是起始符号和末尾符号，且 \\(\vdash \notin \Sigma \wedge \dashv \notin \Sigma\\)
-   \\(t, r\\) 分别是接受状态和拒绝状态，且 \\(t \ne r\\)
-   \\(\delta : (Q \setminus \\{t, r\\}) \times (\Sigma \cup \\{\vdash, \dashv\\}) \rightarrow Q \times \\{L, R\\}\\)
    -   如果 \\(\delta(q, a) = \\{p, L\\}\\) 则表示状态转移后讲读头向左移动一个方格，指向前一个字符
    -   如果 \\(\delta(q, a) = \\{p, R\\}\\) 则表示状态转移后读头向右移动移位，指向下一个字符
    -   \\(\forall q \in Q \setminus \\{t, r\\}. \delta(q, \vdash) = (p, R)\ (p \in Q)\\)
    -   \\(\forall q \in Q \setminus \\{t, r\\}. \delta(q, \dashv) = (p, L)\ (p \in Q)\\)

</div>

<div class="definition">

设 2DFA \\[M = (Q, \Sigma, \vdash, \dashv, \delta, q\_0, t, r)\\]，其接受的语言为

\\[L(M) = \\{x | q\_0 x \vdash^{\*} xt\\}\\]

</div>

有趣的是，2DFA 也被称为**只读图灵机**（read-only Turing Machine），因为它长度有限且无法在纸带上打印东西。

<div class="theorem">

2DFA 与 FA 等价。

</div>

<div class="proof">

显然 DFA \\(\in\\) 2DFA，因此只要证明 \\(2DFA \in DFA\\).

设 2DFA \\[M = (Q\_1, \Sigma, \vdash, \dashv, s, \delta\_1, t, r)\\]，下面构造 NFA \\(M' = (Q\_2, \Sigma, \delta\_2, q\_0, F)\\)。

注意到 2DFA 的状态仅与读头位置和当前状态相关。

假设目前状态为 \\(q\\)，将需要读入的串 \\(x = yz\\) 分为两段，2DFA 的读头可以若干次穿越两段的分割点。将其穿越分割点后的状态记录下来，称其为**有效穿越序列**（valid crossing sequence）。

设有效穿越序列 \\(C = q\_1 q\_2 \dots q\_n\\) 如果 2DFA 接受这个串，那么：

-   有效穿越序列的长度满足 \\(|C| \equiv 1 (\mod 2)\\)
-   有效穿越序列的第一个状态一定是向右的，并且后面顺序一定是左右交替，并且最后一次穿越是向右的
-   \\(\forall q\_i, q\_j \in C. q\_i = q\_j \rightarrow |j-i| \equiv 1 (\mod 2)\\)，即同样的状态在 \\(C\\) 中的位置不可能同奇同偶
    -   “同奇同偶”说明读头两次在同一位置出现了重复的状态，说明状态机陷入了循环，这个字符串无法到达终止状态
    -   由鸽巢定理，容易知道 \\(|C| < 2|Q\_1|\\)，即同一位置的有效穿越序列有限，数量不超过 \\(|Q|^{2|Q|}\\)

由上面的性质，考虑将当前读头所在位置所对应的有效穿越序列编码为 NFA 的状态。NFA 在某个位置的状态，对应 2DFA 读入这个串后在这个位置留下的有效穿越序列。NFA 的读头只能从左向右移动，每次读入一个字符，然后 NFA 状态会转移到下一个位置的有效穿越序列。当然，由于 2DFA 可能采取不同的路径来回穿越下一个位置，因此下一个位置的有效穿越序列有很多种可能，所以这里需要使用 NFA。

为了能够定义有效穿越序列的匹配，下面首先需要定义左匹配与右匹配。自动机在一个位置上向右运动穿越字符时，前后位置对应的有效穿越序列称为右匹配；反之，称为左匹配。当 2DFA 接受字符串后，每个位置的有效穿越序列的最后一次移动都是向右的，因此此时每个位置和它右侧相邻位置的有效穿越序列构成右匹配。所以 NFA 的状态转移之间需要存在右匹配关系。

设存在两个有效穿越序列 \\(C\_1 = [p\_i], C\_2 = [q\_j]\\)，下面针对读头在两个位置和其移动方向进行讨论：

-   \\(C\_1 = \varepsilon, C\_2 = \varepsilon\\) 互为左右匹配
-   如果 \\(C\_1\\) 是 \\(C\_2\\) 的左匹配，即读头在 \\(C\_1\\) 上，且 \\(\delta\_1(p\_l, a) = (q\_k, R)\\)，那么 \\(C\_2 q\_k\\) 是 \\(C\_1 p\_l\\) 的右匹配
-   如果 \\(C\_2\\) 是 \\(C\_1\\) 的右匹配，即读头在 \\(C\_2\\) 上，且 \\(\delta\_1(q\_k, a) = (p\_l, R)\\)，那么 \\(C\_1 p\_l\\) 是 \\(C\_2 q\_k\\) 的左匹配
-   如果 \\(C\_1\\) 是 \\(C\_2\\) 的左匹配，即读头在 \\(C\_1\\) 上，且 \\(\delta\_1(p\_l, a) = (p', L)\\)，那么 \\(C\_1 p\_l\\) 是 \\(C\_2\\) 的左匹配
-   如果 \\(C\_2\\) 是 \\(C\_1\\) 的右匹配，即读头在 \\(C\_2\\) 上，且 \\(\delta\_1(q\_k, a) = (q', R)\\)，那么 \\(C\_2 q\_k\\) 是 \\(C\_1\\) 的右匹配

下面是更加严格的定义：

-   \\(Q\_2 = \\{C = [q\_1 q\_2 \dots q\_n] | \text{$C$ is a valid crossing sequence for $M$}\\}\\)
-   \\(\delta\_2([p\_i], a) = \\{[q\_j] | \text{$[q\_j]$ right matches $p[l]$} \\}\\)
-   \\(q\_0 = [s]\\)
-   \\(F = \\{[p\_i t]\\}\\)

下面简单证明一下 \\(L(M) = L(M')\\)。根据上面的构造显然有 \\(L(M) \subseteq L(M')\\)；而在 \\(M\_2\\) 中，假设存在 \\(\delta\_2([p\_i], a) = [q\_j]\\)，即 \\([q\_j]\\) 是 \\([p\_i]\\) 右匹配，根据上面对于有效穿越序列匹配的讨论实际上就构建了可以被 \\(M\\) 所接受的字符串，因此 \\(L(M') \subseteq L(M)\\)。

构造完成后，又由于 \\(DFA = NFA\\)，因此有 \\(2DFA \in DFA\\)。

</div>

类似可以定义 2NFA。


### 带输出的 FA {#带输出的-fa}

带输出的 FA 分为两类：Moore 机和 Mealy 机。

<div class="definition">

**(Moore 机)**

Moore 机是一个六元组 \\(M = (Q, \Sigma, \Delta, \delta, \lambda, q)\\)：

-   \\(Q, \Sigma, q\_0, \delta\\) 的意义同 FA
-   \\(\Delta\\) 是输出字母表
-   \\(\lambda\\) 是输出函数，\\(\lambda : Q \rightarrow \Delta\\)，其中 \\(\lambda (q) = a\\) 表示在状态 \\(q\\) 下会输出 \\(a\\)

</div>

<div class="definition">

**(Mealy 机)**

Mealy 机是一个六元组 \\(M = (Q, \Sigma, \Delta, \delta, \lambda, q)\\)：

-   \\(Q, \Sigma, q\_0, \delta\\) 的意义同 FA
-   \\(\Delta\\) 是输出字母表
-   \\(\lambda\\) 是输出函数，\\(\lambda : Q \times \Sigma \rightarrow \Delta\\)，其中 \\(\lambda (q, a) = d\\) 表示在状态 \\(q\\) 下读入 \\(a\\) 会输出 \\(d\\)

</div>

读入相同的串，moore 机和 mealy 机表现不同：

-   Moore 机输出 \\(\lambda(q\_0) \lambda(q\_1) \dots \lambda(q\_n)\\)，长度为 \\(n + 1\\)
-   Mealy 机输出 \\(\lambda(q\_0, a\_1) \lambda(q\_1, a\_2) \dots \lambda(q\_n, a\_{n-1})\\)，长度为 \\(n\\)

<div class="definition">

**(Moore 机和 Mealy 机的等价性)**

对于 moore 机 \\(M\_1(Q\_1, \Sigma, \Delta, \delta\_1, \lambda\_1, q\_{01})\\) 和 mealy 机 \\(M\_2(Q\_2, \Sigma, \Delta, \delta\_2, \lambda\_2, q\_{02})\\)，如果 \\(\forall x \in \Sigma^\*, T\_1(x) = \lambda\_1(q\_0) T\_2(x)\\)，则称二者等价。

</div>

事实上，moore 机的描述能力和 mealy 机是等价的，因此对于任意的机器，可以构造与之等价的另一种机器。

<div class="theorem">

Moore 机与 Mealy 机描述能力等价。

</div>

<div class="proof">

下面给出二者互相转换的思路。

-   Moore to Mealy：只要将状态前移半个周期即可。设 Moore 机 \\(M\_1 = (Q, \Sigma, \Delta, \delta, \lambda\_1, q)\\)，令 Mealy 机 \\(M\_2 = (Q, \Sigma, \Delta, \delta, \lambda\_2, q)\\)，其中

    \\[\forall x : \Sigma, \delta(p, x) = q \wedge \lambda\_1(q) = a \rightarrow \lambda(p, x) = a \\]

-   Mealy to Moore：考虑将每种转移来的路径对应到一个状态，用 \\([p, q, x]\\) 表示从 \\(p\\) 转移到 \\(q\\)，造成转移读取的字符为 \\(x\\)。令 Mealy 机为 \\(M\_1 = (Q\_1, \Sigma, \Delta, \delta\_1, \lambda\_1, q)\\)，Moore 机为 \\(M\_2 = (Q\_2, \Sigma, \Delta, \delta\_2, \lambda\_2, q)\\)，则
    -   \\(Q\_2 = \\{ [p, q, x] | \delta\_1(p, q) = x, p \in Q\_1, q \in Q\_1 \\}\\)
    -   \\(\forall p : \delta(p, x) = q. \forall r : \delta(q, y) = r. \delta([p, q, x], y) = [q, r, y]\\)
    -   \\(\forall [p, q, x] \in Q\_2, \lambda\_2([p, q, x]) = \lambda\_1(p, x)\\)

</div>
