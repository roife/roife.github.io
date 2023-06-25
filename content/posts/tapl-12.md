+++
title = "[TaPL] 12 Normalization"
author = ["roife"]
date = 2021-09-28
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论", "程序语义", "STLC"]
draft = false
+++

## Normalization {#normalization}

<div class="definition">

**(Normalization)**

一个程序会在有限步内停机，则称其为 **normalizable** (strongly normalizable)。

设 \\(t \rightarrow t\_1 \rightarrow t\_2 \rightarrow \dots t\_n \nrightarrow\\)，则 \\(t\_n\\) 为 \\(t\\) 的 **normal form**。

</div>

STLC 中的 well-typed 的表达式都是 normalizable 的，即 STLC 满足 normalization。但是大多数语言都不满足 normalization 的特性，因为他们往往包括递归或递归类型。


## Normalization for STLC {#normalization-for-stlc}

证明 normalization 不能靠长度来证明，因为在 substitution 的过程中，代入的值可能会被替换多次，此时长度会变长。

这里需要给出一个更强的 induction hypothesis：对于类型 \\(T\\)，用 \\(R\_T\\) 表示 \\(T\\) 的 closed terms 的集合。并且 \\(R\_t(t) \Leftrightarrow t \in R\_T\\)。（\\(R\_T\\) 一般被称作 saturated sets 或 reducibility candidates）。

<div class="definition">

**\\(R\_A(t)\\)**

-   \\(R\_A(t)\\) iff \\(t\\) halts.
-   \\(R\_{T\_1 \rightarrow T\_2}(t)\\) iff \\(t\\) halts and \\(\forall s \in R\_{T\_1}. R\_{T\_2}(t\ s)\\)

</div>

从定义中可以看到，对于函数类型而言不仅要求函数自己会停机，并且对于任意可停机的输入，这个函数都可以停机。 这里称 \\(t : A\\) 拥有性质 \\(P\\)，而函数 \\(f : A \rightarrow A\\) 能保持性质 \\(P\\)。

要证明 normalization，需要分为两步：

-   所有满足 \\(R\_T(t)\\) 的 term \\(t\\) 都会停机
-   所有 term \\(t\\) 都满足 \\(R\_T(t)\\)

第一步是显然的：

<div class="lemma">

If \\(R\_T(t)\\), then \\(t\\) halts.

</div>

<div class="proof">

Immediately.

</div>

第二步分成两个 Lemmas 来证明：

<div class="lemma">

If \\(t : T\\) and \\(t \rightarrow t'\\), then \\(R\_T(t)\\) iff \\(R\_T(t')\\)。

</div>

<div class="proof">

证明如下：

-   \\(T = A\\), trivial
-   \\(T = T\_1 \rightarrow T\_2\\)
    -   \\(\Longrightarrow\\)：设 \\(R\_T(t)\\) 且 \\(R\_{T\_1}(s)\\)，则有 \\(t'\ s = t\ s \in R\_{T\_2}\\)，得证
    -   \\(\Longleftarrow\\)：同理

</div>

下面正式证明所有 term \\(t\\) 都满足 \\(R\_T(t)\\)。其中难点是对 λ abstraction 的证明，因为要证明 \\(\lambda x : T\_1 . t\_2 \in R\_{T\_1 \rightarrow T\_2}\\)，就要证明 \\(R\_{T\_2}(t\_2)\\)，但是 \\(t\_2\\) 中存在自由变量 \\(x\\)，而 \\(R\_{T\_2}\\) 是定义在 closed terms 上的，因此不能证明 \\(R\_{T\_2}(t\_2)\\) 。这里采取的方法是证明对 open term \\(t\\) 的所有 closed instances 都满足性质。

<div class="lemma">

If
\\[x\_1 : T\_1, \dots x\_n : T\_n \vdash t : T\\]
\\[v\_1:T\_1, \dots, v\_n:T\_n\\]
\\[\forall i \in 1 \dots n. \text{$v\_i$ is closed value and $v\_i \in R\_{T\_i}$}\\]
, then \\(R\_T([x\_1 \mapsto v\_1] \dots [x\_n \mapsto v\_n] t)\\).

</div>

<div class="proof">

证明如下：

-   `T-Var` \\(t = x\_i\\)，\\(T = T\_i\\) 显然
-   `T-Abs`
    -   \\(t = \lambda x : S\_1 . s\_2\\)
    -   \\(x\_1 : T\_1, \dots, x\_n : T\_n, x:S\_1 \vdash s\_2 : S\_2\\)
    -   \\(T = S\_1 \rightarrow S\_2\\)
    -   \\([x\_1 \mapsto v\_1] \dots [x\_n \mapsto v\_n]\ t\\) 是一个 value，满足第一条。要证明 \\(R\_{S\_1 \rightarrow S\_2}(t)\\)，只需要再证明
        \\[\forall s : S\_1, R\_{S\_2}(([x\_1 \mapsto v\_1] \dots [x\_n \mapsto v\_n]\ t)\ s)\\]

    -   设 \\(s : S\_1 \text{ and } R\_{S\_1}(s)\\)，则存在 \\(s \rightarrow^\* v\\)。根据归纳假设有 \\(R\_{S\_2}([x\_1 \mapsto v\_1] \dots [x\_n \mapsto v\_n][x \mapsto v]\ s\_2)\\)。即

        \\[
             (\lambda x : S\_1. [x\_1 \mapsto v\_1] \dots [x\_n \mapsto v\_n] s\_2)\ s \rightarrow^\* [x\_1 \mapsto v\_1] \dots [x\_n \mapsto v\_n][x \mapsto v]s\_2 \in R\_{S\_2}
             \\]

    -   由前面的 Lemma 知 \\(\forall s : S\_1, R\_{S\_2}((\lambda x : S\_1. [x\_1 \mapsto v\_1] \dots [x\_n \mapsto v\_n] s\_2)\ s)\\)

-   `T-App`
    -   \\(t = t\_1\ t\_2\\)
    -   \\(x\_1 : T\_1, \dots, x\_n : T\_n \vdash t\_1 : T\_{11} \rightarrow T\_{12}, t\_2 : T\_{11}\\)
    -   \\(T = T\_{12}\\)
    -   由归纳假设知 \\(R\_{T\_{11} \rightarrow T\_{12}}([x\_1 \mapsto v\_1] \dots [x\_n \mapsto v\_n] t\_1)\\) 且 \\(R\_{T\_{11}}([x\_1 \mapsto v\_1] \dots [x\_n \mapsto v\_n] t\_2)\\)
    -   根据 \\(R\_{T\_1 \rightarrow T\_2}(t)\\) 的定义有 \\(R\_{T\_{12}}([x\_1 \mapsto v\_1] \dots [x\_n \mapsto v\_n] (t\_1\ t\_2))\\)

</div>

由上面两个 Lemmas，则可以证明 STLC 的 normalization 性质。

<div class="corollary">

**(Normalization for STLC)**

In STLC, if \\(\vdash t : T\\), then \\(t\\) is normalizable.

</div>
