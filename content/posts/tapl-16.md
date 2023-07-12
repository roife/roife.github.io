+++
title = "[TaPL] 16 Metatheory of Subtyping"
author = ["roife"]
date = 2023-07-07
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论", "程序语义", "subtyping"]
draft = true
+++

前面使用的 subtyping rules 并不适合实际实现，因为它们并不是自底向上构建的，主要问题在于下面两个规则：

-   `T-Sub`

    \\[\dfrac{\Gamma \vdash t : S \quad S <: T}{\Gamma \vdash t : T} \tag{T-Sub}\\]

    其他大部分 typing rules 都是对于某个特殊结构进行类型推导（syntax-directed），而 `T-Sub` 的推导对象是一个 metavar \\(t\\)，因此这条规则总可以对一个 term 使用，且目标类型 \\(T\\) 是未知的，需要程序来决断使用的时机。

-   `S-Trans`

    \\[\dfrac{S <: U \quad U <: T}{S <: T} \tag{S-Trans}\\]

    `S-Trans` 也有类似的问题。并且除此之外，`S-Trans` 在使用时需要程序自己推理出一个中间变量 \\(U\\)，这对程序来说是很困难的。

-   `S-Refl`

    \\[S <: S \tag{S-Refl}\\]

    `S-Refl` 中没有假设条件，因此这一条也是在任何时候都可以使用的，它也不是 syntax-directed 的。

因此本章使用新的 typing rules 替代原有的规则（称为 declarative relation），称为 **algorithmic subtyping** 和 **algorithmic typing**，其推断过程是 syntax-directed 的。然后会证明这些规则和原有规则是等价的（即可以互相推导）。


## Algorithmic Subtyping {#algorithmic-subtyping}

Typechecker 在判断 \\(S <: T\\) 时会判断 \\((S, T)\\) 是否包含在 \\(\mapsto S <: T\\)（称为 \\(S\\) is algorithmically a subtype of \\(T\\)） 中。Algorithmic subtyping relation 里中去掉了 `S-Trans` 和 `S-Refl` 这两条规则，并让这两条规则直接蕴含在其他具体的规则中。

首先，对于之前 record types 定义了三条规则，分别是 `S-RcdDepth` / `S-RcdWidth` 和 `S-RcdPerm`。这三条规则在使用时往往需要配合 `S-Trans` 使用，因此这里将这三条规则合并为 `S-Rcd`。

\\[\dfrac{\\{l\_{i}^{i \in 1 \dots n}\\} \subseteq \\{k\_{j}^{j \in 1 \dots m}\\} \quad k\_j = l\_i \rightarrow S\_j <: T\_i}{\\{k\_{j} : S\_j^{j \in 1 \dots m}\\} <: \\{l\_{i} : T\_i^{i \in 1 \dots n}\\} } \tag{S-Rcd}\\]

{{< figure src="/img/in-post/post-tapl/16-1-subtype-relation-with-records.png" caption="<span class=\"figure-number\">Figure 1: </span>Subtype relation with records" >}}

<div class="lemma">

If \\(S <: T\\) is derivable from the subtyping rules including `S-RcdDepth=`, `S-RcdWidth`, and `S-RcdPerm` (but not `S-Rcd`), then it can also be derived using `S-Rcd` (and not `S-RcdDepth`, `S-Rcd-Width`, or `S-Rcd-Perm`), and vice versa.

</div>

<div class="lemma">

下面证明 `S-Refl` 和 `S-Trans` 在上面的规则中都是不必要的。

1.  \\(S <: S\\) can be derived for every type \\(S\\) without using `S-Refl`.
2.  If \\(S <: T\\) is derivable, then it can be derived without using `S-Trans`.

</div>

<div class="proof">

只要证明 `S-Refl` 和 `S-Trans` 都可以用其他规则表示即可。第一个 lemma 直接对 \\(S\\) 的结构进行归纳即可，因此下面主要证明第二个 lemma。

下面对 derivations 的**大小**进行归纳，即假设比当前 derivations 小的都成立。如果 derivations 中应用的最后一条规则不是 `S-Trans`，那么根据归纳假设，前面的部分也可以不用 `S-Trans`，成立。因此下面考虑最后一条规则是 `S-Trans` 的情况。即存在两个 subderivations \\(S <: U\\) 和 \\(U <: T\\)，并且两个 subderivations 中都没有用到 `S-Trans`。

-   Any / `S-Top`：直接替换成 `S-Top`
-   `S-Top` / Any：则 `U = Top`，则 `T` 也是 `Top`，那么右侧一定是 `S-Top`，归于第一条
-   `S-Arrow` / `S-Arrow`：

    \begin{aligned}
    & S = S\_1 \rightarrow S\_2 \\\\
    & U = U\_1 \rightarrow U\_2 \\\\
    & T = T\_1 \rightarrow T\_2
    \end{aligned}

    \begin{aligned}
    & U\_1 <:S\_1 & S\_2 <:U\_2 \\\\
    & T\_1 <:U\_1 & U\_2 <:T\_2
    \end{aligned}

    因此在两个 subderivations 中分别推导了 \\(S\_i\\) 和 \\(U\_i\\) 以及 \\(U\_i\\) 和 \\(T\_i\\) 的关系。
-   `S-Rcd` / `S-Rcd`：类似 `S-Arrow` / `S-Arrow`
-   `S-Arrow` / `S-Rcd` 和 `S-Rcd` / `S-Arrow`：不可能

</div>
