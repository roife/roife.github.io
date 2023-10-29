+++
title = "[形式语言] 04 Context-free Grammar"
author = ["roife"]
date = 2023-10-15
series = ["formal-language-and-automata"]
tags = ["形式语言"]
draft = false
+++

## 派生 {#派生}


### 派生树 {#派生树}

<div class="definition">

**(派生树)**

设 CFG \\(G = (V, T, P, S)\\)，\\(G\\) 的派生树满足下面的条件的一棵（有序）树：

-   树的每个顶点都有一个标记 \\(X \in V \cup T \cup \\{\varepsilon\\}\\)
-   树根的标记为 \\(S\\)
-   如果一个非叶结点的标记为 \\(A\\)，其从左到右的儿子的标记依次为 \\(X\_1 X\_2 \dots X\_n\\)，则 \\(A \rightarrow X\_1 X\_2 \dots X\_n \in P\\)。
-   如果一个叶子结点的标记为 \\(X\\)，则 \\(X \in V\\)
-   如果一个顶点的标记是 \\(\varepsilon\\)，那么这是一个叶子结点，且它是其父节点的唯一儿子

满足除第二条定义外的规则的树称为**派生子树**（derivation subtree），顶点为 \\(A\\) 也可以称为 \\(A\\) 子树。

</div>

<div class="definition">

**(结果)**

设有文法 \\(G\\) 的一棵派生树 \\(T\\) 的所有叶子顶点从左到右依次标记为 \\(X\_1, X\_2, \dots, X\_n\\)，则称符号串 \\(X\_1, X\_2, \dots, X\_n\\) 是 \\(T\\) 的**结果**（yield）。

</div>

<div class="theorem">

设 CFG \\(G = (V, T, P, S)\\)，\\(S \xRightarrow{\*} \alpha\\) 的充要条件是 \\(G\\) 有一棵结果为 \\(\alpha\\) 的派生树。

</div>

<div class="proof">

为了方便，先证明一个更一般的结论：对于任意 \\(A \in V\\)，\\(A \xRightarrow{\*} \alpha\\) 的充要条件是 \\(G\\) 有一棵结果为 \\(\alpha\\) 的 \\(A\\) 子树。

-   下面证明充分性。设 \\(G\\) 有一棵结果为 \\(a\\) 的 \\(A\\) 子树，对这棵子树的非叶顶点数量 \\(n\\) 进行归纳
    -   \\(n = 1\\)，那么树的高度为 \\(2\\)，设结点 \\(A\\) 的叶结点从左到右分别为 \\(X\_1 X\_2 \dots X\_n\\)，根据定义有 \\(A \rightarrow X\_1 X\_2 \dots X\_n \in P\\)，又因为该子树结果为 \\(\alpha\\)，因此 \\(X\_1 X\_2 \dots X\_n = \alpha\\)，即 \\(A \xRightarrow{\*} \alpha\\)
    -   设 \\(n \le k\\) 时命题成立，那么当 \\(n = k+1\\) 时，设 \\(A\\) 的儿子从左到右分别为 \\(X\_1 X\_2 \dots X\_m\\)，则根据定义必有 \\(A \rightarrow X\_1 X\_2 \dots X\_m \in P\\)。设 \\(X\_i\\) 的结果为 \\(\alpha\_i\\)，根据归纳假设有 \\(X\_i \xRightarrow{\*} \alpha\_i\\)，且 \\(\alpha = \alpha\_1 \alpha\_2 \dots \alpha\_m\\)，因此
        \\[A \xRightarrow{} X\_1 X\_2 \dots X\_m \xRightarrow{\*} \alpha\_1 X\_2 \dots X\_m \xRightarrow{\*} \alpha\_1 \alpha\_2 \dots X\_m \xRightarrow{\*} \dots \xRightarrow{\*} \alpha\_1 \alpha\_2 \dots \alpha\_m \\]

-   下面证明必要性。设 \\(A \xRightarrow{n} \alpha\\)，下面对派生步数进行归纳。
    -   \\(n=1\\)，那么 \\(A \Rightarrow \alpha \in P\\)，令 \\(\alpha = X\_1 X\_2 \dots X\_m\\)，则存在 \\(A \Rightarrow X\_1 X\_2 \dots X\_m\\) 子树，成立。
    -   设 \\(n = k\\) 时成立，则当 \\(n = k + 1\\) 时，设派生为

        \\[A \xRightarrow{} X\_1 X\_2 \dots X\_m \xRightarrow{\*} \alpha\_1 X\_2 \dots X\_m \xRightarrow{\*} \alpha\_1 \alpha\_2 \dots X\_m \xRightarrow{\*} \dots \xRightarrow{\*} \alpha\_1 \alpha\_2 \dots \alpha\_m \\]

        其中 \\(X\_i \Rightarrow \alpha\_i\\)。当 \\(X\_i = \alpha\_i\\) 时，\\(X\_i\\) 子树只有一个 \\(X\_i\\) 结点；当 \\(X\_i \xRightarrow{+} \alpha\_i\\) 时，由归纳假设，存在一棵结果为 \\(\alpha\_i\\) 的 \\(X\_i\\) 子树。又由于 \\(A \Rightarrow X\_1 X\_2 \dots X\_m\\)，因此存在一棵 \\(A\\) 子树使得叶结点为 \\(X\_i\\)。此时将上面对应的 \\(X\_i\\) 子树接到 \\(X\_i\\) 上，即得到了一棵结点为 \\(\alpha\\) 的 \\(A\\) 子树。

综上所述，命题成立。

</div>


### 最左派生和最右派生 {#最左派生和最右派生}

<div class="definition">

**(最左派生)**和**(最右派生)**

设 CFG \\(G = (V, T, P, S)\\)，
\\(\alpha\\) 是 \\(G\\) 的一个句型，如果存在派生使得 \\(\alpha\\) 中的每一步都是对当前句型中的最左变量进行替换，则该派生称为**最左派生**（leftmost derivation），相应的规约叫**最右规约**（rightmost derivation）。中间得到的每一个句型都称为**左句型**（left sentence form）。

反之，如果 \\(\alpha\\) 中的每一步都是对当前句型中的最右变量进行替换，则该派生称为**最右派生**（rightmost derivation），相应的规约叫**最左规约**（leftmost derivation）。中间得到的每一个句型都称为**右句型**（right sentence form）。

</div>

由于计算机处理输入串时是从左到右进行的，因此称最左规约为**规范规约**（normal reduction），对应的派生为**规范派生**（normal derivation），对应的句型为**规范句型**（normal sentence form）。

<div class="definition">

如果 \\(\alpha\\) 是 CFG \\(G\\) 中的一个句型，那么 \\(G\\) 中存在 \\(\alpha\\) 的最左派生和最右派生。

</div>

<div class="proof">

首先证明最左派生的情况，对派生的步数 \\(n\\) 进行归纳。

-   `n = 1`，此时就是最左派生，显然成立
-   设当 \\(1 \le n \le k\\) 时都成立，那么当 \\(n = k+1\\) 时，设

    \\[A \xRightarrow{} X\_1 X\_2 \dots X\_m \xRightarrow{\*} \alpha\_1 X\_2 \dots X\_m \xRightarrow{\*} \alpha\_1 \alpha\_2 \dots X\_m \xRightarrow{\*} \dots \xRightarrow{\*} \alpha\_1 \alpha\_2 \dots \alpha\_m \\]

    其中对于每一步 \\(X\_i \xRightarrow{n\_i} \alpha\_i\\)，都有 \\(n\_i \le k\\)，因此存在一个最左派生 \\(X\_i \xRightarrow{n\_i} \alpha\_i\\)。令上面的每一步 \\(X\_i \xRightarrow{n\_i} \alpha\_i\\) 都采取最左派生，从而上面派生的每一步都是最左派生，因此这个派生即为 \\(A \xRightarrow{\*} \alpha\\) 的最左派生。

最右派生的证明同理。

</div>

用反证法可以证明派生树与最左派生、最右派生是一一对应的。


### 二义性 {#二义性}

<div class="definition">

**(二义性)**

设 CFG \\(G = (V, T, P, S)\\)，如果存在 \\(w \in L(G)\\) 使得 \\(w\\) 至少存在两棵不同的派生树，则称 \\(G\\) 是有**二义性的**（ambiguity）。

</div>

注意二义性是文法的性质，而不是语言的性质。一个语言的众多文法中有的是有二义性的，有的是没有二义性的。

判定一个 CFG 是否存在二义性是一个不可解的问题。

一些文法可以通过某种方式修复成没有二义性的语法，但是有一些语言是不存在非二义性的，称为**固有二义性的**（inherent ambiguity）或先天二义性的。

例如 \\(\\{0^i 1^j 2^k | i = j \vee j = k\\}\\) 的所有文法都是固有二义性的，这是因为语言本身就蕴含了一种“或”的关系，对于 \\(0^n 1^n 2^n\\) 这样的句子可以走两条派生的路径，且它们最终都能推出这个句子。


### 自顶向下分析和自底向上分析 {#自顶向下分析和自底向上分析}

判定一个句子是否属于一个文法对应的语言时，可以采取从起始符号派生为句子的方式，也可以采用从句子规约到起始符的方式，前者称为自顶向下的分析，后者称为自底向上的分析。


## 上下文无关文法的化简 {#上下文无关文法的化简}


### 无用符号 {#无用符号}

<div class="definition">

设 CFG \\(G = (V, T, P, S)\\)，对于任意 \\(X \in V \cup T\\)，如果存在 \\(w \in L(G)\\) 使得 \\(w\\) 的派生过程中存在 \\(X\\)（即 \\(\exists \alpha, \beta \in (V \cup T)^{\*}. S \xRightarrow{\*} \alpha X \beta \xRightarrow{\*} w\\)），则称 \\(X\\) 是**有用的**，否则称为是无用的。

</div>

注意终结符也有可能是无用的，因此需要考虑 \\(V \cup T\\) 内的所有字符。

这个定义实际上包含了两层，即要求 \\(S \xRightarrow{\*} \alpha X \beta\\)，又要求 \\(\alpha X \beta \xRightarrow{\*} w\\)。在两个条件下发现无用符号的方法类似，分别是从起始符号和终结符集开始，将能够从已有集合的符号所组成的派生/规约得到的符号加入到集合中，并求这个过程的闭包。

<div class="pseudocode">

\begin{algorithm}
  \caption{Remove Unused Symbols}
  \begin{algorithmic}
    \procedure{StartFromTerminators}{CFG $G = (V, T, P, S)$}
    \state initialize $SV$ as $\\{ A | A \rightarrow w \in P \wedge w \in T^{\*} \\}$
    \repeat
      \state $SV \gets SV \cup \\{A | A \rightarrow \alpha \in P \wedge \alpha \in (T \cup Q)^{\*}\\}$
    \until{$SV$ is unchanged in this iteration}
    \state $V' \gets SV$
    \state $P' \gets \\{ A \rightarrow \alpha | A \rightarrow \alpha \in P \wedge A \in V' \wedge a \in (T \cup V')^{\*} \\}$
    \return $G' \gets (V', T, P', S)$
    \endprocedure
    \procedure{StartFromStarter}{CFG $G = (V, T, P, S)$}
    \state initialize $SV$ as $\\{S\\} \cup \\{ A | S \rightarrow \alpha A \beta \in P \\}$
    \state initialize $ST$ as $\\{ s | S \rightarrow \alpha a \beta \in P \\}$
    \repeat
      \state $SV \gets SV \cup \\{B | A \in SV \wedge A \rightarrow \alpha B \beta \in P \\}$
      \state $ST \gets ST \cup \\{a | A \in SV \wedge A \rightarrow \alpha a \beta \in P \\}$
    \until{both $SV$ and $ST$ are unchanged in this iteration}
    \state $V' \gets SV$
    \state $P' \gets SP$
    \state $P' \gets \\{ A \rightarrow \alpha | A \rightarrow \alpha \in P \wedge A \in V' \wedge a \in (T \cup V')^{\*} \\}$
    \return $G' \gets (V', T', P', S)$
    \endprocedure
  \end{algorithmic}
\end{algorithm}

</div>

值得注意的是，上面两个过程必须先执行 `StartFromTerminators`（无法导出终结串），然后执行 `StartFromStarter`（起始符号不可达）。例如 \\(S \rightarrow AB; A \rightarrow a; B \rightarrow Bb\\)，显然这个语言是一个空集，然后如果先执行第二步，再执行第一步，会发现 \\(S, A, C\\)，并不会被删除，需要再次执行第二步。

这是因为【删除不能导出终结串】的符号可能会产生新的【从起始符号不可达】的符号，但是【删除从起始符号不可达】的字符串并不会产生新的【不能导出终结串】的符号。


### 去除空串 {#去除空串}

<div class="definition">

形如 \\(A \rightarrow \varepsilon\\) 的产生式称为**空产生式**（null production）。对于 \\(G = (V, T, P, S)\\) 中的任何非终结符 \\(A\\)，如果 \\(A \xRightarrow{+} \varepsilon\\)，则称 \\(A\\) 是**可空**（nullable）变量。

</div>

寻找可空变量可以从 \\(A \rightarrow \varepsilon\\) 这样的产生式开始，寻找一个闭包：

<div class="pseudocode">

\begin{algorithm}
  \caption{Find Nullable Variables}
  \begin{algorithmic}
    \procedure{main}{CFG $G = (V, T, P, S)$}
    \state initialize $U$ as $\\{ A | A \rightarrow \varepsilon \in P \\}$
    \repeat
      \state $U \gets U \cup \\{A | A \rightarrow \alpha \in P \wedge \alpha \in U^{\*}\\}$
    \until{$U$ is unchanged in this iteration}
    \return $U$
    \endprocedure
  \end{algorithmic}
\end{algorithm}

</div>

化简时不能直接删除会产生空产生式的推导。在去除空串时，需要先求出可空变量集合 \\(U\\)。对于 \\(A \rightarrow X\_1 X\_2 \dots X\_n\\)，，令 \\(A \rightarrow \alpha\_1 \alpha\_2 \dots \alpha\_n\\)，其中

-   如果 \\(X\_i \in U\\)，那么 \\(\alpha\_i = X\_i\\) 或 \\(\alpha\_i = ε\\)
-   否则 \\(\alpha\_i = X\_i\\)
-   \\(\alpha\_1, \alpha\_2, \dots, \alpha\_n\\) 不能同时为空


### 去除单一产生式 {#去除单一产生式}

<div class="definition">

形如 \\(A \rightarrow B\\) 的产生式称为**单一产生式**（unit production）。

</div>

例如在语法分析时，\\(E \rightarrow T + T | T \* T | T\\) 中包含的 \\(E \rightarrow T\\) 就是单一产生式。

单一产生式的去除方法很简单：

如果 \\(A \rightarrow X | B; B \rightarrow C | D\\)，那么只要将 \\(B\\) 的产生式移上来即可，即 \\(A \rightarrow X | C | D; B \rightarrow C | D\\)，这个过程可能又会产生新的单一产生式，因此需要迭代进行达到不动点为止。


## 乔姆斯基范式 {#乔姆斯基范式}

<div class="definition">

如果 CFG \\(G = (V, T, P, S)\\) 中的所有产生式都具有形式

\\[A \rightarrow BC\\]
\\[A \rightarrow a\\]

其中 \\(A, B, C \in V\\)，\\(a \in T\\)，则称 \\(G\\) 为**乔姆斯基范式文法**（Chomsky normal form），简称 CNF。

</div>

CNF 的特点是它的语法树是一颗类似二叉树的形式。

对于一个普通的文法，转换为 CNF 的步骤如下：

1.  先经过去除无用符号、去除空产生式和单一产生式的化简。此时文法形如

    \\[A \rightarrow X\_1 X\_2 \dots X\_n\ (X\_i \in V \cup T)\\]
    \\[A \rightarrow a\\]

2.  对于每个终结符 \\(a \in T\\)，添加 \\(T\_a \in V\\)，并添加 \\(T\_a \rightarrow a \in P\\)，再将原来所有出现 \\(a\\) 的地方都替换为 \\(T\_a\\)。此时文法形如

    \\[A \rightarrow B\_1 B\_2 \dots B\_n\ (B\_i \in V)\\]
    \\[T\_a \rightarrow a\\]

3.  进一步将 \\(A \rightarrow B\_1 B\_2 \dots B\_n\\) 进行拆解，令 \\(C\_i \rightarrow B\_i B\_{i+1} \dots B\_n\\)，则

    \\[A \rightarrow B\_1 C\_2\\]
    \\[C\_2 \rightarrow B\_2 C\_3\\]
    \\[\dots\\]
    \\[C\_{n-1} \rightarrow B\_{n-1} B\_n\\]
    \\[T\_a \rightarrow a\\]


## 格雷巴赫范式 {#格雷巴赫范式}

<div class="definition">

如果 CFG \\(G = (V, T, P, S)\\) 中的所有产生式都具有形式

\\[A \rightarrow aB\\]

其中 \\(A \in V\\)，\\(B \in V^{\*}\\)，\\(a \in T\\)，则称 \\(G\\) 为**格雷巴赫范式**（Greibach normal form），简称 GNF。

</div>

根据定义，GNF 中的文法只有两种形式：

\\[A \rightarrow a\\]
\\[A \rightarrow a B\_1 B\_2 \dots B\_m (m \ge 1)\\]

右线性文法是一种特殊的 GNF。

<div class="definition">

在文法中如果存在形如 \\(A \xRightarrow{n} \alpha A \beta\\) 的派生，则称该派生为变量 \\(A\\) 的递归派生。

如果 \\(n = 1\\) 则称为是直接递归（directly recursive），否则称为间接递归（indirectly recursive）。

当 \\(\alpha = \varepsilon\\) 时，称为左递归（left-recursive）；当 \\(\beta = \varepsilon\\) 时，称为右递归（right-recursive）。

</div>

GNF 的特点在于它消除了所有左递归。

将一个普通的文法转换为 GNF 的步骤如下：

1.  先经过去除无用符号、去除空产生式和单一产生式的化简。此时文法形如

    \\[A \rightarrow X\_1 X\_2 \dots X\_n\ (X\_i \in V \cup T)\\]
    \\[A \rightarrow a\\]

2.  对于 \\(A \rightarrow \alpha\\)，如果满足 \\(\alpha \in T \cup V^{+} \cup TV^{+}\\)，则不作处理；否则对于 \\(\alpha = X\_1 X\_2 \dots X\_m\\)。如果 \\(X\_i (i \ge 2) = a \in T\\)，则加入产生式 \\(T\_a \rightarrow a\\)，并用 \\(T\_a\\) 代替所有出现 \\(a\\) 的地方，此时文法形如

    \\[A \rightarrow B\_1 B\_2 \dots B\_n\ (B\_i \in V)\\]
    \\[A \rightarrow a B\_1 B\_2 \dots B\_n\\]
    \\[A \rightarrow a\\]

3.  下面考虑去除文法中的左递归，打破文法中左递归的循环。设 \\(V\_1 = \\{A\_1, A\_2, \dots, A\_m\\}\\)

    -   对于 \\(A\_i \rightarrow A\_j \alpha\ (i > j)\\)，用 \\(A\_j\\) 的产生式 \\(A\_j \rightarrow \beta\_1 | \beta\_2 | \dots | \beta\_n\\) 替换右部的第一个 \\(A\_j\\)，得到 \\(A\_i \rightarrow \beta\_1 \alpha | \beta\_2 \alpha | \dots | \beta\_n \alpha\\)
    -   对于 \\(A\_i \rightarrow A\_i \alpha\_1 | A\_i \alpha\_2 | \dots | A\_i \alpha\_n | \beta\_1 | \beta\_2 | \dots | \beta\_m\\)，其中 \\(\beta\_j\\) 不以 \\(A\_i\\) 开头，经过第一步后也不以 \\(A\_j\ (j < i)\\) 开头，将 \\(A\_i\\) 的产生式替换为下面的产生式集

        \\[A\_i \rightarrow \beta\_1 | \beta\_2 | \dots | \beta\_m\\]
        \\[A\_i \rightarrow \beta\_1 B | \beta\_2 B | \dots | \beta\_m B\\]
        \\[B \rightarrow \alpha\_1 | \alpha\_2 | \dots | \alpha\_n\\]
        \\[B \rightarrow \alpha\_1B | \alpha\_2B | \dots | \alpha\_nB\\]

    经过上面两步，保证了文法的形式如下

    \\[A\_i \rightarrow A\_j \alpha\ (i < j)\\]
    \\[A\_i \rightarrow a \alpha\\]
    \\[A\_i \rightarrow a\\]
    \\[B\_i \rightarrow \alpha\\]
4.  设 \\(V = \\{A\_1 \cup A\_2 \cup \dots \cup A\_n\\} \cup \\{B\_1 \cup B\_2 \cup \dots \cup B\_m\\}\\)，则 \\(A\_n\\) 已经符合要求，因此需要从 \\(A\_n\\) 开始，对于 \\(i > j\\) 将 \\(A\_i\\) 逐步代回到 \\(A\_j\\) 中。此时 \\(A\_i\\) 都符合要求，接下来对 \\(B\_i\\) 进行同样的化简操作即可。

    考虑到每次经过这个步骤，对于单个产生式 \\(A\_i \rightarrow A\_j\alpha\\) 产生的 \\(B \rightarrow \alpha\\)，其右侧的符号数量 \\(|\alpha|\\) 是递减的（\\(|A\_j \alpha| < |\alpha|\\)），因此算法能够终止。


## 自嵌套文法 {#自嵌套文法}

<div class="definition">

设 CFG \\(G = (V, T, P, S)\\) 是化简过的文法，如果 \\(G\\) 中存在形如

\\[A \xRightarrow{+} \alpha A \beta\\]

的派生，则称 \\(G\\) 是**自嵌套文法**（self-embedding grammar），其中 \\(\alpha, \beta \in (V \cup T)^{+}\\)。

</div>

自嵌套文法可以是正则语言，例如 \\(S \rightarrow 0S0 | 0S | 0\\)；但是非自嵌套文法一定是正则语言。
