+++
title = "[TaPL] 08 Typed Arithmetic Expressions"
author = ["roife"]
date = 2021-05-01
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论", "程序语义"]
draft = false
+++

## Types {#types}

在 Chapter 3 中定义的 Untyped Arithmetic Expression 存在 stuck 的情况，例如 `pred false`。为了检查出这些错误，我们引入“类型”的概念。对于 Chapter 3 的表达式，需要用到 `Nat` 和 `Bool` 两种类型。

这里说 "term `t` has type `T`" 是不经过 evaluation 的情况下得到的信息。

例如 \\(\operatorname{\mathtt{if}} \operatorname{\mathtt{true}} \operatorname{\mathtt{then}} \operatorname{\mathtt{false}} \operatorname{\mathtt{else}} \operatorname{\mathtt{true}}\\) 的类型一定是 `Bool`，可以由规则推导得到；但是 \\(\operatorname{\mathtt{if}} (\operatorname{\mathtt{iszero}} 0) \operatorname{\mathtt{then}} 0 \operatorname{\mathtt{else}} \operatorname{\mathtt{false}}\\) 的具体类型则需要在 evaluation 后才能得到。


## The Typing Relation {#the-typing-relation}

一个 typing relation \\(t \in T\\) 通常写作 \\(t : T\\)，由一些从 type 到 term 的推导规则来指定。

{{< figure src="/img/in-post/post-tapl/8-1-typing-rules-for-booleans.png" caption="<span class=\"figure-number\">Figure 1: </span>Typing rules for booleans" >}}

{{< figure src="/img/in-post/post-tapl/8-2-typing-rules-for-numbers.png" caption="<span class=\"figure-number\">Figure 2: </span>Typing rules for numbers" >}}

如图的 `T-If` 规则，要求 \\(t\_1 : \operatorname{\mathtt{Bool}}\\)，同时 \\(t\_2\\) 和 \\(t\_3\\) 为同一种类型 \\(T\\)。

<div class="definition">

**(Well typed)**

A term \\(t\\) is **typable** (or **well typed**) if there is some \\(T\\) such that \\(t : T\\).

</div>


### Inversion {#inversion}

<div class="lemma">

**(Inversion of the typing relation)** (Generation Lemma)

1.  If \\(\operatorname{\mathtt{true}} : R\\), then \\(R = \operatorname{\mathtt{Bool}}\\).
2.  If \\(\operatorname{\mathtt{false}} : R\\), then \\(R = \operatorname{\mathtt{Bool}}\\).
3.  If \\(\operatorname{\mathtt{if}} t\_1 \operatorname{\mathtt{then}} t\_2 \operatorname{\mathtt{else}} t\_3 : R\\), then \\(t\_1 : \operatorname{\mathtt{Bool}}, t\_2 : R, t\_3 : R\\).
4.  If \\(0 : R\\), then \\(R = Nat\\).
5.  If \\(\operatorname{\mathtt{succ}} t\_1 : R\\), then \\(R = \operatorname{\mathtt{Nat}}\\) and \\(t\_1 : \operatorname{\mathtt{Nat}}\\).
6.  If \\(\operatorname{\mathtt{pred}} t\_1 : R\\), then \\(R = \operatorname{\mathtt{Nat}}\\) and \\(t\_1 : \operatorname{\mathtt{Nat}}\\).
7.  If \\(\operatorname{\mathtt{iszero}} t\_1 : R\\), then \\(R = \operatorname{\mathtt{Bool}}\\) and \\(t\_1 : \operatorname{\mathtt{Nat}}\\).

</div>

<div class="proof">

此处 typing rules 都是双射，易证。

</div>

通过 generation lemma，可以根据 term 的 syntactic form 来计算出其 type。类型的推导（typing derivation）可以也用一棵树来表示。

-   **Statements** are formal assertions about the typing of programs.
-   **Typing rules** are implications between statements
-   **Derivations** are deductions based on typing rules.


### Uniqueness {#uniqueness}

<div class="theorem">

**(Uniqueness of Types)**

Each term \\(t\\) has at most one type. That is, if \\(t\\) is typable, then its type is unique. Moreover, there is just one derivation of this typing built from the inference rules.

**注解** 这条规则对于 subtyping 不适用

</div>


## Safety = Progress + Preservation {#safety-progress-plus-preservation}

类型系统最基本的特征在于 safety（soundness），即 well-typed 的 term 不会出错（陷入 stuck state）。这个性质包括两点：

-   **Progress**: A well-typed term is not stuck
    -   either it is a value
    -   or it can take a step according to the evaluation rules
-   **Preservation**: If a well-typed term takes a step of evaluation, then the resulting term is also well-typed.
    -   而且大部分时候 evaluation 不会改变 type（但是 subtyping 中一个类型可能会变得 smaller）


### Progress Theorem {#progress-theorem}

<div class="lemma">

**(Canonical Forms)**

1.  If \\(v\\) is a value of type `Bool`, then \\(v\\) is either `true` or `false`
2.  If \\(v\\) is a value of type `Nat`, then \\(v\\) is a numeric value according to the grammar in Figure 3-2.

</div>

<div class="proof">

Values 有四种可能：`true`、`false`、`0`、`succ nv`。根据 inversion lemma 4 和 5 可知后两种情况的类型是 `Nat`，排除。故命题 1 成立。

同理可证明命题 2。

</div>

<div class="theorem">

**(Progress)**

Suppose \\(t\\) is a well-typed term (\\(t : T\\)). Then either \\(t\\) is a value or else there is some \\(t'\\) with \\(t \rightarrow t'\\).

</div>

<div class="proof">

By induction on a derivation of \\(t : T\\)

对于 `T-True`、`T-False`、`T-Zero` 显然成立，因为此时已经是 value。

-   `T-If`

    \\[
      \operatorname{\mathtt{if}} t\_1 \operatorname{\mathtt{then}} t\_2 \operatorname{\mathtt{else}} t\_3 \quad (t\_1 : \operatorname{\mathtt{Bool}})
      \\]

    -   如果 \\(t\_1\\) 是 value，则根据 canonical forms lemma，它一定是 `true` 或者 `false`，则可以应用 `E-IfTrue` 或者 `E-IfFalse`
    -   否则可以对 \\(t\_1\\) 使用 `E-If`

-   `T-Pred`

    \\[
      t = \operatorname{\mathtt{pred}} t\_1 \quad (t\_1 : \operatorname{\mathtt{Nat}})
      \\]

    -   如果 \\(t\_1\\) 是 value，则根据 canonical forms lemma，它一定是 `0` 或者 `succ nv`，则可以应用 `E-PredZero` 或者 `E-PredSucc`
    -   否则可以使用 `E-Pred`

-   `T-Succ` / `T-IsZero` 同上

</div>


### Preservation Theorem {#preservation-theorem}

<div class="theorem">

**(Preservation)**

If \\(t : T\\) and \\(t \rightarrow t'\\), then \\(t' : T\\).

</div>

<div class="proof">

By induction on a derivation of \\(t : T\\)

-   `T-True` / `T-False` / `T-Zero` 排除，此时无法进行 evaluation

-   `T-If`

    \\[
      \operatorname{\mathtt{if}} t\_1 \operatorname{\mathtt{then}} t\_2 \operatorname{\mathtt{else}} t\_3 \quad (t\_1 : \operatorname{\mathtt{Bool}}; t\_2, t\_3 : T)
      \\]

    -   `E-True` / `E-False`

        \\(t\_1\\) 为 `true` / `false`，结果为 \\(t\_2\\) / \\(t\_3\\)。此时表达式的类型均为 `T`

    -   `E-If`

        \\(t\_1 \rightarrow t\_1'\\)，由归纳假设知 \\(t\_1' : \operatorname{\mathtt{Bool}}\\)，再由 canonical forms lemma 和 `T-If` 知 \\(\operatorname{\mathtt{if}} t\_1' \operatorname{\mathtt{then}} t\_2 \operatorname{\mathtt{else}} t\_3 : T\\)，则命题成立

-   `T-Succ`

    \\[
      t = \operatorname{\mathtt{succ}} t\_1
      \\]

    此时只能用 `E-Succ` 这条规则使得 \\(t \rightarrow t'\\)，即只要证明 `succ t' : Nat`。由归纳假设知 `t' : Nat`，则成立。

</div>

Preservation theorem 也被称为 **subject reduction** / **subject evaluation**。这个名称来自于 \\(t : T\\) 表示 "\\(t\\) has type \\(T\\)"，其中 \\(t\\) 是句子的 subject。


### Type Safe {#type-safe}

在所有的类型系统（包括 subtyping）中，这两个定理都成立，否则就不是 type-safe 的。

但是存在一些特殊情况。例如使用 small-step 形式化 Java 的 operational semantics 时，preservation 就不再成立了。但是使用 big-step 就不会有这个问题，所以还是认为它是 type-safe 的。

几个有趣的问题：

<div class="question">

`E-PredZero` 这条规则看起来比较违反直觉，能不能直接去掉？

</div>

<div class="answer">

不能，因为这样会破坏 progress property。要去掉的话需要使用 exception。或者使用 intersection type/dependent type 定义严格的“正数”。

</div>

<div class="question">

Subject reduction 的逆操作 subject expansion（若 \\(t \rightarrow t'\\) 且 \\(t' : T\\)，则 \\(t : T\\)）成立吗？

</div>

<div class="answer">

错误，\\(\operatorname{\mathtt{if}} \operatorname{\mathtt{false}} \operatorname{\mathtt{then}} \operatorname{\mathtt{true}} \operatorname{\mathtt{else}} 0 \rightarrow 0\\)，而前者是 ill-typed。

</div>

<div class="question">

对于 big-step 语义如何保证类型安全？

</div>

<div class="answer">

-   **Preservation** (similar) If a well-typed term evaluates to some final value, then this value has the same type as the original term.
-   **Progress** (stronger) Every well-typed term can be evaluated to some final value. (Evaluation always terminates on well-typed terms.)

**注解** 在 big-step 中 Progress property 并不总是成立的（例如在支持 general recursion 的语言中），因为没有办法区分 error state 和 termination。一个解决方案是为此提供一个前面提到过的 explicit wrong translation。

</div>
