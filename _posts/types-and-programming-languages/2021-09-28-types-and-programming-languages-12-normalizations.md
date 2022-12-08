---
layout: "post"
title: "「TaPL」 12 Normalization"
subtitle: "Normalizations for types"
author: "roife"
date: 2021-09-28

tags: ["Types and Programming Languages@读书笔记", "读书笔记@Tags", "类型系统@程序语言理论", "程序语言理论@Tags", "Normalization@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

- `normalizable`：一个 well-typed 程序会在有限步内停机（这里指的是 STLC）

但是大多数语言都不满足 normalization 的特性，因为他们往往包括递归或递归类型。

# Normalization for Simple Types

证明 normalization 不能靠长度来证明，因为在 substitution 的过程中，代入的值可能会被替换多次，此时长度会变长。

这里首先需要给出一个更强的 induction hypothesis：对于类型 $T$，用 $R_T$ 表示 $T$ 的 closed terms 的集合。并且 $R_t(t) \Leftrightarrow t \in R_T$。（$R_T$ 一般被乘坐 saturated sets 或 reducibility candidates）。

> **Definitions**: $R_A(t)$
>
> - $R_A(t)$ iff $t$ halts.
> - $R_{T_1 \rightarrow T_2}$ iff $t$ halts and whenever $R_{T_1}(s)$ we have $R_{T_2}(t\ s)$

从定义中可以看到，对于函数类型而言不仅要求函数自己会停机，并且对于任意可停机的输入，这个函数都可以停机。
这里称 $t : A$ 拥有性质 $P$，而函数 $f : A \rightarrow A$ 能保持性质 $P$。

要证明 normalization，需要分为两步：
- 所有满足 $R_T(t)$ 的 term $t$ 都会停机
- 所有 term $t$ 都满足 $R_T(t)$

第一步是显然的：

> **Lemma** If $R_T(t)$, then $t$ halts. (Immediately)

第二步分成两个 Lemmas 来证明：

> **Lemma** If $t : T$ and $t \rightarrow t'$, then $R_T(t)$ iff $R_T(t')$。
>
> **Proof**
>
> - 如果 $T = A$ 那么显然成立，即 $t$ 停机 iff $t'$ 停机
> - 如果 $T = T_1 \rightarrow T_2$
>   + $\Longrightarrow$：设 $R_T(t)$ 且 $R_{T_1}(s)$，则有 $R_{T_2}(t'\ s)$。又因为 $t\ s \rightarrow t'\ s$，则 $R_{T_2}(t'\ s)$。
>   + $\Longleftarrow$：同理

下面正式证明所有 term $t$ 都满足 $R_T(t)$。其中难点是对 λ abstraction 的证明，因为要证明 $\lambda x : T_1 . t_2 \in R_{T_1 \rightarrow T_2}$，就要证明 $R_{T_2}(t_2)$，但是 $t_2$ 中存在自由变量（即 $t_2$ 不封闭），所以不能直接采用这种证明方式。这里采取的方法是证明对 open term $t$ 的所有 closed instances 都满足。

> **Lemma** If $x_1 : T_1, \dots x_n : T_n \vdash T$ and $v_1, \dots, v_n$ are closed values of types $T_1 \dots T_n$ with $R_{T_i}(v_i)$ for each $i$, then $R_T([x_1 \mapsto v_1] \dots [x_n \mapsto v_n] t)$.
>
> **Proof**
>
> - `T-Var` $t = x_i$，$T = T_i$ 显然
> - `T-Abs` $t = \lambda x : S_1 . s_2$，$x_1 : T_1, \dots, x_n : T_n, x:S_1 \vdash s_2 : S_2$，$T = S_1 \rightarrow S_2$
>    + 首先 $[x_1 \mapsto v_1] \dots [x_n \mapsto v_n]t$ 已经是一个 value，所以只要证明 $\forall s : S_1, R_{S_2}(([x_1 \mapsto v_1] \dots [x_n \mapsto v_n] t) s)$。
>    + 记 $s \rightarrow^* v$ 是一个 value，则 $R_{S_1}(v)$。根据归纳假设有 $R_{S_2}([x_1 \mapsto v_1] \dots [x_n \mapsto v_n][x \mapsto v] s_2)$。即
>
>       $$
>       (\lambda x : S_1. [x_1 \mapsto v_1] \dots [x_n \mapsto v_n] s_2)\ s \rightarrow^* [x_1 \mapsto v_1] \dots [x_n \mapsto v_n][x \mapsto v]s_2
>       $$
>
>    + 由前面的 Lemma 知 $R_{S_2}((\lambda x : S_1. [x_1 \mapsto v_1] \dots [x_n \mapsto v_n] s_2)\ s)$ 对任意的 $s$ 都成立。
> - `T-App` $t = t_1\ t_2$，$x_1 : T_1, \dots, x_n : T_n \vdash t_1 : T_{11} \rightarrow T_{12}$，$x_1 : T_1, \dots, x_n : T_n \vdash t_2 : T_{11}$，$T = T_{12}$
>    + 由递归假设知 $R_{T_{11} \rightarrow T_{12}}([x_1 \mapsto v_1] \dots [x_n \mapsto v_n] t_1)$ 且 $R_{T_{11}}([x_1 \mapsto v_1] \dots [x_n \mapsto v_n] t_2)$
>    + 则 $R_{T_{12}}([x_1 \mapsto v_1] \dots [x_n \mapsto v_n] (t_1\ t_2))$

由上面两个 Lemmas，则可以证明 STLC 的 normalization 性质。

> **Theorem** Normalization
>
> If $\vdash t : T$, then $t$ is normalizable.
