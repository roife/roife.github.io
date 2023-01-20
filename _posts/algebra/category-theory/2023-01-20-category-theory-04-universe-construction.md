---
layout: "post"
title: "「范畴论」04 泛构造"
subtitle: "Universal construction"
author: "roife"
date: 2023-01-20

tags: ["代数@数学", "数学@Tags", "Haskell@编程语言", "范畴论@数学"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 初始对象和终极对象

一些范畴内有两种特殊的对象：
- 对于范畴 $\mathcal{C}$，如果 $\forall A \in \operatorname{\mathrm{Ob}}(\mathcal{C})$ 都有**唯一**态射 $\mathbf{0} \rightarrow A$，则 $\mathbf{0}$ 称为**初始对象**（initial object）
  + $\operatorname{\mathrm{Hom}}(\mathbf{0}, A)$ 恰有一个元素
- 对于范畴 $\mathcal{C}$，如果 $\forall A \in \operatorname{\mathrm{Ob}}(\mathcal{C})$ 都有**唯一**态射 $A \rightarrow \mathbf{1}$，则 $\mathbf{1}$ 称为**终极对象**（terminal object）
  + $\operatorname{\mathrm{Hom}}(A, \mathbf{1})$ 恰有一个元素
- 如果既是初始对象，又是终端对象，则称为零对象。

![Initial object and Terminal object](/img/in-post/post-algebra/initial-terminal-object.svg){:height="200px" width="200px"}

注意，初始对象不意味着没有其它对象到它的态射，而是只强调它发出的态射；终端对象也只强调其它对象到它的态射，它自己也可以发出态射。

范畴中的初始对象与终极对象**唯一同构（unique up to isomorphism）**：
- 如果存在另一个初始对象 $\mathbf{0'}$，那么 $\mathbf{0} \simeq \mathbf{0'}$
- 如果存在另一个终极对象 $\mathbf{1'}$，那么 $\mathbf{1} \simeq \mathbf{1'}$

Hask 范畴内的初始对象与终极对象分别为 `Void` 与 `Unit`（这里不考虑 `undefined`，否则 Haskell 就无法给出范畴的初始对象和终极对象了）：

```haskell
data Void
data Unit = Unit

absurd :: Void -> a
absurd = absurd

unit :: a -> Unit
unit _ = Unit
```

`()` 和 `Unit` 同构，其它空对象也和 `Void` 同构：

```haskell
data V
data U = U

vphi :: V -> Void
vphi = vphi

vpsy :: Void -> V
vpsy = absurd

uphi :: U -> Unit
uphi U = Unit

upsy :: Unit -> U
upsy Unit = U
```

# 积与余积

## 范畴上的积

范畴上的积是笛卡尔积的抽象，定义如下：

> 设 $A, B, C \in \mathcal{C}$，$A$ 与 $B$ 的**积**（product）记作 $A \times B$，其存在态射 $\pi\_1 : A \times B \rightarrow A$ 与 $\pi\_2 : A \times B \rightarrow B$，使得对于所有 $f : C \rightarrow A$ 与 $g : C \rightarrow B$，存在**唯一**态射 $\langle f, g \rangle : C \rightarrow A \times B$ 使下图交换：
>
> ![Product](/img/in-post/post-algebra/product.svg){:height="300px" width="300px"}
>
> 其中，$\pi\_1$ 和 $\pi\_2$ 称为态射（projection）。
>
> 即 $\pi\_1 \circ \langle f, g \rangle = f$ 且 $\pi\_2 \circ \langle f, g \rangle = g$。如果所有这样的积存在，那么它们都与 $A \times B$ 唯一同构。

> **积的融合**：在一个存在积的范畴上，设存在 $h : C' \rightarrow C$，则 $\langle f, g \rangle \circ h = \langle f \circ h, g \circ h \rangle$，即下图交换：
>
> ![Product Merge](/img/in-post/post-algebra/product-merge.svg){:height="300px" width="300px"}
>
> **证明**：首先 $\langle f, g \rangle = \langle \pi\_1 \circ \langle f, g \rangle, \pi\_2 \circ \langle f, g \rangle \rangle$
>
> $\text{Right} = \langle (\pi\_1 \circ \langle f, g \rangle) \circ h, (\pi\_2 \circ \langle f, g \rangle) \circ h \rangle = \langle \pi\_1 \circ (\langle f, g \rangle \circ h), \pi\_2 \circ (\langle f, g \rangle \circ h) \rangle = \text{Left}$

在上面的融合中，$C'$ 的态射 $f'$ 可以用 $f \circ h$ 表达，因此 $C$ 比 $C'$ 更“泛化”；同理 $A \times B$ 比 $C$ 更“泛化”，因此只有 $A \times B$ 被称为积。例如在集合范畴上，$A \times B$ 就是笛卡尔积 $(a, b)$。

在 Haskell 中，$\langle f, g \rangle$ 可以定义为 `<.>`：

```haskell
(<.>) :: (a -> b) -> (a -> c) -> a -> (b,c)
(<.>) f g a = (f a, g a)

pi1 :: (a, b) -> a
pi1 (a, b) = a

pi2 :: (a, b) -> b
pi2 (a, b) = b
```

## 积函子与积范畴

> 积运算 $\times : \mathcal{C\_1} \times \mathcal{C\_2} \rightarrow \mathcal{D}$ 是一个二元函子（称为**积函子**），给定 $f\_1 : X \rightarrow X'$ 和 $f\_2 : Y \rightarrow Y'$，可以定义映射：
>
> $$
> f_1 \times f_2 = \langle f_1 \circ \pi_1, f_2 \circ \pi_2 \rangle : X \times Y \rightarrow X' \times Y'
> $$
>
> 如下图：
>
> ![Product Functor](/img/in-post/post-algebra/product-functor.svg){:height="400px" width="400px"}

积函子可以将范畴映射到对应的积范畴 $\mathcal{C} \times \mathcal{D}$：
- 对象 $\operatorname{\mathrm{Ob}}(\mathcal{C} \times \mathcal{D}) = \\{ X \times Y \ \vert \ X \in \operatorname{\mathrm{Ob}}(\mathcal{C}),\ Y \in \operatorname{\mathrm{Ob}}(\mathcal{D}) \\}$
- 态射 $\operatorname{\mathrm{Arr}}(\mathcal{C} \times \mathcal{D}) = \\{ f \times g : A\_1 \times A\_2 \rightarrow B\_1 \times B\_2 \ \vert \ f : A\_1 \rightarrow B\_1 \in \operatorname{\mathrm{Arr(\mathcal{C})}},\ g : A\_2 \rightarrow B\_2 \in \operatorname{\mathrm{Arr(\mathcal{D})}} \\}$
- 恒等态射 $\operatorname{\mathrm{id}}_{(X, Y)} = \operatorname{\mathrm{id}}\_{\mathcal{C}} \times \operatorname{\mathrm{id}}\_{\mathcal{D}}$
- 态射复合 $(f \times g) \circ (h \times k) = (f \circ h) \times (g \circ k)$
- 这个定义还可以推广到 $n$ 维：设 $\\{ \mathcal{C}\_i : i \in I \\}$，则积范畴 $\prod_{i \in I}\mathcal{C}\_i$ 的定义如下：
  + $\operatorname{\mathrm{Ob}}(\prod_{i \in I} \mathcal{C}\_i) = \prod\_{i \in I}\operatorname{\mathrm{Ob}}(\mathcal{C}\_i)$
  + $\operatorname{\mathrm{Hom}}\_{\prod\_{i \in I} \mathcal{C}\_i}((X\_i)\_i, (Y\_i)\_i) = \prod\_{i \in I}\operatorname{\mathrm{Hom}}_{\mathrm{C}\_i}(X\_i, Y\_i)$

> **积函子的融合**：在一个存在积的范畴 $\mathcal{C}$ 上，对于对象 $A, B, A', B'$，若有 $f : C \rightarrow A, g : C \rightarrow B, k\_1 : A \rightarrow A', k\_2 : B \rightarrow B'$，则 $(k\_1 \times k\_2) \circ \langle f, g \rangle = \langle k\_1 \circ f, k\_2 \circ g \rangle$
>
> ![Product Functor Merge](/img/in-post/post-algebra/product-functor-merge.svg){:height="450px" width="450px"}
>
> **证明**：$(k\_1 \times k\_2) \circ \langle f, g \rangle = \langle k\_1 \circ \pi\_1 , k\_2 \circ \pi\_2 \rangle \circ \langle f, g \rangle = \langle k\_1 \circ \pi\_1 \circ \langle f, g \rangle , k\_2 \circ \pi\_2 \circ \langle f, g \rangle \rangle = \langle k\_1 \circ f, k\_2 \circ g \rangle$

由积函子的融合定律可以得到态射复合：

$$
(f \times g) \circ (h \times k)
= (f \times g) \circ \langle h \circ \pi_1, k \circ \pi_2 \rangle = \langle f \circ h \circ \pi_1, g \circ k \circ \pi_2 \rangle = (f \circ h) \times (g \circ k)
$$

![Product Composition](/img/in-post/post-algebra/product-composition.svg){:height="400px" width="400px"}

## 范畴上的余积（和）

范畴上的余积是不相交并集的抽象，又称为和（sum）或不相交并集（disjoint union），定义如下：

> 设 $A, B, C \in \mathcal{C}$，$A$ 与 $B$ 的**余积**（coproduct）记作 $A + B$，其存在态射 $i\_1 : A \rightarrow A + B$ 与 $i\_2 : B \rightarrow A + B$，使得对于所有 $f : A \rightarrow C$ 与 $g : B \rightarrow C$，存在**唯一**态射 $[f, g] : A + B \rightarrow C$ 使下图交换：
>
> ![Coproduct](/img/in-post/post-algebra/coproduct.svg){:height="300px" width="300px"}
>
> 其中，$i\_1$ 和 $i\_2$ 称为注入映射（injection map）。
>
> 即 $i\_1 \circ [f, g] = f$ 且 $i\_2 \circ [f, g] = g$。如果所有这样的余积存在，那么它们都与 $A + B$ 唯一同构。
>
> $[f, g]$ 的定义如下：
>
> $$
> [f, g](x) =
> \begin{cases}
> f(x), &x = A, \\
> g(x), & x = B
> \end{cases}
> $$

$[f, g]$ 对应了 `either` 函数：

```haskell
either ::(a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left x) = f x
either _ g (Right y) = g y
```

两个注入函数则分别就是 `Either` 的构造器 `Left` 和 `Right`。

不难发现积和余积是对偶的，上面谈过的积相关的性质对余积都有对偶的性质，但是余积的态射是分段定义的，因此比范畴积的定义要麻烦很多。

> 余积的融合：$h \circ [f, g] = [h \circ f, h \circ g]$

> 余积运算 $+ : \mathcal{C\_1} \times \mathcal{C\_2} \rightarrow \mathcal{D}$ 是一个二元函子（称为**余积函子**），给定 $f\_1 : X \rightarrow X'$ 和 $f\_2 : Y \rightarrow Y'$，可以定义映射：
>
> $$
> f_1 + f_2 = [i_1' \circ f_1, i_2' \circ f_2] : X + Y \rightarrow X' + Y'
> $$
>
> $$ (f_1 + f_2)(x) =
> \begin{cases}
> (i_1' \circ f_1)(x), & x = X \\
> (i_2' \circ f_2)(x), & x = Y
> \end{cases}
> $$
>
> 如下图：
>
> ![Coproduct Functor](/img/in-post/post-algebra/coproduct-functor.svg){:height="400px" width="400px"}

> 余积函子的融合：$[f, g] \circ (k\_1 + k\_2) = [f \circ k\_1, g \circ k\_2]$

余积范畴：$\mathcal{C} + \mathcal{D}$：
- 对象 $\operatorname{\mathrm{Ob}}(\mathcal{C} + \mathcal{D}) = \\{ X + Y \ \vert \ X \in \operatorname{\mathrm{Ob}}(\mathcal{C}),\ Y \in \operatorname{\mathrm{Ob}}(\mathcal{D}) \\}$
- 态射 $\operatorname{\mathrm{Arr}}(\mathcal{C} + \mathcal{D}) = \\{ f + g : A\_1 + A\_2 \rightarrow B\_1 + B\_2 \ \vert \ f : A\_1 \rightarrow B\_1 \in \operatorname{\mathrm{Arr(\mathcal{C})}},\ g : A\_2 \rightarrow B\_2 \in \operatorname{\mathrm{Arr(\mathcal{D})}} \\}$
- 恒等态射 $\operatorname{\mathrm{id}}_{(X, Y)} = \operatorname{\mathrm{id}}\_{\mathcal{C}} + \operatorname{\mathrm{id}}\_{\mathcal{D}}$
- 态射复合 $(f + g) \circ (h + k) = (f \circ h) + (g \circ k)$
- 这个定义还可以推广到 $n$ 维：设 $\\{ \mathcal{C}\_i : i \in I \\}$，则余积范畴 $\amalg_{i \in I}\mathcal{C}\_i$ 的定义如下：
  + $\operatorname{\mathrm{Ob}}(\amalg_{i \in I} \mathcal{C}\_i) = \amalg\_{i \in I}\operatorname{\mathrm{Ob}}(\mathcal{C}\_i)$
  + $\operatorname{\mathrm{Hom}}\_{\amalg\_{i \in I} \mathcal{C}\_i}(X_j, X_k) = \operatorname{\mathrm{Hom}}\_{C\_j}(X\_j, X\_k) \ \\{ j = k \\}\ \operatorname{\mathrm{or}}\ \emptyset\ \\{ j \ne k \\}\ (\forall j \in I, X\_j \in \operatorname{\mathrm{Ob}}(C\_j))$
