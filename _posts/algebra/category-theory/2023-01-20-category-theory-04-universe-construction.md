---
layout: "post"
title: "「范畴论」04 泛构造"
subtitle: "Universal construction, comma category, pullback and pushout"
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
> 其中，$\pi\_1$ 和 $\pi\_2$ 称为投影（projection）。
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

$$\operatorname{\mathrm{Ob}}(\prod_{i \in I} \mathcal{C}_i) = \prod_{i \in I}\operatorname{\mathrm{Ob}}(\mathcal{C}_i)$$

$$\operatorname{\mathrm{Hom}}_{\prod_{i \in I} \mathcal{C}_i}((X_i)_i, (Y_i)_i) = \prod_{i \in I}\operatorname{\mathrm{Hom}}_{\mathrm{C}_i}(X_i, Y_i)$$

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

$$\operatorname{\mathrm{Ob}}(\coprod_{i \in I} \mathcal{C}_i) = \coprod_{i \in I}\operatorname{\mathrm{Ob}}(\mathcal{C}_i)$$

$$
\operatorname{\mathrm{Hom}}_{\coprod_{i \in I} \mathcal{C}_i}(X_j, X_k) =
\begin{cases}
\operatorname{\mathrm{Hom}}_{C_j}(X_j, X_k), & j = k \\
\emptyset, & j \ne k
\end{cases}
\quad (\forall j \in I, X_j \in \operatorname{\mathrm{Ob}}(\mathcal{C}_j))
$$

# 逗号范畴

对于函子 $\mathcal{A} \overset{S}{\rightarrow} \mathcal{C} \overset{T}{\leftarrow} \mathcal{B}$，定义逗号范畴 $(S / T)$ 如下：
- 对象：形如 $(A, B, f)$，其中 $A \in \operatorname{\mathrm{Ob}}(\mathcal{A}), B \in \operatorname{\mathrm{Ob}}(\mathcal{B}), f : SA \rightarrow TB \in \operatorname{\mathrm{Arr}}(\mathcal{C})$；
- 态射：态射 $(A, B, f) \rightarrow (A', B', f')$ 形如 $(g, h)\ (g : A \rightarrow A' \in \operatorname{\mathrm{Arr}}(\mathcal{A}), h : B \rightarrow B' \in \operatorname{\mathrm{Arr}}(\mathcal{B}))$，使得下图交换：
![Comma Category](/img/in-post/post-algebra/comma-category.svg){:height="200px" width="200px"}
  + 态射合成：$(g\_1, h\_1) \circ (g\_2, h\_2)$ = $(g\_1 \circ g\_2, h\_1 \circ h\_2)$
  + 单位态射：$(\operatorname{\mathrm{id}}\_A, \operatorname{\mathrm{id}}\_B)$

从定义中可以得到显然的两个投影函子 $P : (S/T) \rightarrow A$ 和 $Q : (S/T) \rightarrow B$。

## 切片范畴与箭头范畴

切片范畴和箭头范畴都是逗号范畴的特例。

考虑只包含一个对象 $1$ 和一个单位态射 $\operatorname{\mathrm{id}}\_1$ 的范畴 $\mathbf{1}$。指定对象 $X \in \operatorname{\mathrm{Ob}}(\mathcal{C})$，可以得到函子 $j\_X : \mathbf{1} \rightarrow \mathcal{C}$。

设存在范畴 $\mathcal{C'}$ 及函子 $T : \mathcal{C'} \rightarrow \mathcal{C}$：

- （**余切片范畴**，**仰范畴**，co-slice category）设函子 $\mathbf{1} \overset{j\_X}{\rightarrow} \mathcal{C} \overset{T}{\leftarrow} \mathcal{C'}$，其对应的逗号范畴为 $(j\_X / T)$
  + 对象形如 $(W, X \overset{i}{\rightarrow} TW)\ (W \in \operatorname{\mathrm{Ob}}(\mathcal{C'}))$（省略 $1$）
  + 态射形如 $h : (W\_1, i\_1) \rightarrow (W\_2, i\_2)\ (h : W\_1 \rightarrow W\_2)$ 使下图交换：
  ![Co-slice category](/img/in-post/post-algebra/co-slice-category.svg){:height="250px" width="250px"}
- （**切片范畴**，**俯范畴**，slice category）设函子 $\mathcal{C'} \overset{T}{\rightarrow} \mathcal{C} \overset{j\_X}{\leftarrow} \mathbf{1}$，其对应的逗号范畴为 $(T / j\_X)$
  + 对象形如 $(W, TW \overset{p}{\rightarrow} X)\ (W \in \operatorname{\mathrm{Ob}}(\mathcal{C'}))$（省略 $1$）
  + 态射形如 $f : (W\_1, p\_1) \rightarrow (W\_2, p\_2)\ (f : W\_1 \rightarrow W\_2)$ 使下图交换：
  ![Slice category](/img/in-post/post-algebra/slice-category.svg){:height="250px" width="250px"}

当 $\mathcal{A} = \mathcal{B} = \mathcal{C}$ 时，可以得到**箭头范畴**（arrow category）。设函子 $\mathcal{C} \overset{\operatorname{\mathrm{id}}\_{\mathcal{C}}}{\rightarrow} \mathcal{C} \overset{\operatorname{\mathrm{id}}\_{\mathcal{C}}}{\leftarrow} \mathcal{C}$，即逗号范畴 $(\operatorname{\mathrm{id}}\_{\mathcal{C}}/\operatorname{\mathrm{id}}\_{\mathcal{C}})$：
- 对象为 $\mathcal{C}$ 中的所有态射 $f : X \rightarrow Y$
- 态射形如 $(f : X \rightarrow Y) \rightarrow (f' : X' \rightarrow Y')$ 的交换图：
  ![Arrow category](/img/in-post/post-algebra/arrow-category.svg){:height="200px" width="200px"}
- 箭头范畴也是从范畴 $\mathcal{I} = (\cdot \rightarrow \cdot)$ 到 $\mathcal{C}$ 的函子范畴（$\mathcal{I} = (\cdot \rightarrow \cdot)$ 为只有两个对象和一个非恒等态射的范畴）

# 极限与余极限

## 对角函子与锥形

> 定义**对角函子**（diagonal functor）$\Delta : \mathcal{C} \rightarrow \mathcal{C}^{\mathcal{I}}$，它能将 $\mathcal{C}$ 上的对象映射到函子范畴 $\operatorname{\mathrm{Fct}}(\mathcal{I}, \mathcal{C})$ 中的**常值函子** $\Delta(X)$ 上。即给定 $X \in \operatorname{\mathrm{Ob}}(\mathcal{C})$，有：
>
> $$
> \Delta(X) : \mathcal{I} \rightarrow \mathcal{C} =
> \begin{cases}
> i \mapsto X, & \forall i \in \operatorname{\mathrm{Ob}}(\mathcal{I}) \\
> [i \rightarrow j] \mapsto \operatorname{\mathrm{id}}_X, & \forall [i \rightarrow j] \in \operatorname{\mathrm{Arr}}(\mathcal{I})
> \end{cases}
> $$
>
> 给定态射 $f : X \rightarrow Y \in \operatorname{\mathrm{Arr}}(\mathcal{C})$，范畴 $\mathcal{C}^{\mathcal{I}}$ 中的 $\Delta(f) : \Delta(X) \rightarrow \Delta(Y)$ 是一个自然变换：$\forall i \in \operatorname{\mathrm{Ob}}(\mathcal{I}), \Delta(f)(i) = f$。
>
> ![Diagonal Functor](/img/in-post/post-algebra/diagonal-functor.svg){:height="300px" width="300px"}


> 范畴 $\mathcal{I}$ 是一个小范畴，称为 `Index` 范畴；函子 $F : \mathcal{I} \rightarrow \mathcal{C} = i \mapsto D\_i$ 将范畴 $\mathcal{I}$ 的对象 $i$ 映射为范畴 $\mathcal{C}$ 中的 $D\_i$。
>
> 若存在 $C \in \mathcal{C}$ 和常量函子 $\Delta(C)$，且 $C \rightarrow D\_i$ 的态射 $p\_i$ 为 $\Delta(C) \rightarrow F$ 的自然变换（满是自然性），则称 $C$ 和 $p\_i$ 组成了一个**锥**（cone）。$C$ 为锥的顶点，锥的腰部是自然变换的分量 $p\_i$，锥的底是 $D\_i$。
>
> ![Cone](/img/in-post/post-algebra/cone.svg){:height="600px" width="600px"}
> $p\_i$ 满足自然性，即 $F(i \rightarrow j) \circ p\_i = p\_j$。

## 泛锥与极限

所有的锥可以构成一个锥范畴，范畴中的对象是锥形。但是在 $\mathcal{C}$ 中不是所有对象 $C$ 都能成为锥的顶点，因此 $\Delta(C)$ 和 $D$ 之间可能不存在自然变换。锥之间的态射由锥顶点 $C$ 决定。

> 若对象 $C$ 和 $p\_i : C \rightarrow D\_i$ 组成的锥形是一个所有其他对象 $C'$ 和 $f\_i : C' \rightarrow D\_i$ 组成的锥形的终对象，则称顶点为 $C$ 的锥形对象是函子 $F$ 的**极限**（limit）或极限对象，记为 $\varprojlim(D)$。
>
> ![Limit](/img/in-post/post-algebra/limit.svg){:height="400px" width="400px"}
>
> 即其它顶点 $C'$ 都存在唯一态射 $g : C' \rightarrow \varprojlim(D)$ 使得 $f\_i = p\_i \circ g$。

极限也可以用逗号范畴定义：

> 令 $\mathcal{I}, \mathcal{C}$ 为范畴，设函子 $\beta : \mathcal{I}^{\mathrm{op}} \rightarrow \mathcal{C}$。考虑 $\mathcal{C} \overset{\Delta}{\rightarrow} \operatorname{\mathrm{Fct}}(\mathcal{I}^{\mathrm{op}}, \mathcal{C}) \overset{j\_{\beta}}{\leftarrow} \mathbf{1}$，对应的逗号范畴为 $(\Delta / j\_{\beta})$（或记作 $(\Delta / \beta)$），其中的对象为锥。这个逗号范畴实际上是一个切片范畴，对象为 $(C, f : \Delta(C) \rightarrow \beta)\ (C \in \operatorname{\mathrm{Ob}}(\mathcal{C}), \beta \in \operatorname{\mathrm{Fct}}(\mathcal{I}^{\mathrm{op}}, \mathcal{C}))$ 。
>
> 其中，$C$ 是锥的顶点；$f$ 是自然变换，对应锥的腰部。$f$ 对应了一族态射 $\Delta(C)(i) \rightarrow \beta(i) = C \rightarrow D\_i$。
>
> 逗号范畴 $(\Delta / \beta)$ 中若存在终对象则记作极限 $\varprojlim(\beta)$。

## 余锥与余极限

余锥是锥的对偶，余极限是极限的对偶。

![Co-cone](/img/in-post/post-algebra/cocone.svg){:height="600px" width="600px"}

> 若对象 $C$ 和 $p\_i : D\_i \rightarrow C$ 组成的余锥是一个所有其他对象 $C'$ 和 $f\_i : D\_i \rightarrow C'$ 组成的余锥的始对象，则称顶点为 $C$ 的余锥对象是函子 $F$ 的**余极限**（colimit）或余极限对象，记为 $\varinjlim(D)$。
>
> ![Colimit](/img/in-post/post-algebra/colimit.svg){:height="400px" width="400px"}
>
> 即其它顶点 $C'$ 都存在唯一态射 $g : \varinjlim(D) \rightarrow C'$ 使得 $f\_i = g \circ p\_i$。

## 极限与自然变换

下面讨论极限和自然变换的关系。

![Limit and Natural transformation](/img/in-post/post-algebra/limit-and-natural-transformation.svg){:height="350px" width="350px"}

对于范畴 $\mathcal{C}$ 上的锥集，如果极限存在（即存在泛锥），那么存在**唯一**的态射 $g : C' \rightarrow \varprojlim(D)$，其中态射 $g \in \mathrm{Hom}(C', \varprojlim(D))$。即 $g$ 与 $C'$ 一一对应；对于每个锥（对象） $C'$，都可以找到态射 $g \in \mathrm{Hom}(C', \varprojlim(D))$。这是一个从对象到态射的映射，即一个自然变换。

下面讨论这个自然变换对应的函子。
- 第一个函子能将对象映射到 $g$。$C' \rightarrow \mathrm{Hom}(C', \varprojlim(D))$，即反变 Hom 函子 $\operatorname{\mathrm{Hom}}(-, \varprojlim(D))$
- 第二个函子能将对象映射到锥（对应的自然变换）。$C' \rightarrow \operatorname{\mathrm{Nat}}(\Delta_{C'}, D)$

事实上，第一个函子对应了态射 $g$，第二个函子中的自然变换对应了态射 $f$，且有关系 $f = p \circ g$。其中 $p$ 是固定的，因此 $g \cong f$，即

$$
\operatorname{\mathrm{Nat}}(\Delta_{C'}, \Delta_C) \cong \mathrm{Hom}(C', \varprojlim(D)) \cong \operatorname{\mathrm{Nat}}(\Delta_{C'}, D)
$$

这也是锥映射的交换性条件。

## 极限的例子

### 范畴积与终对象

范畴积可以看成 $\mathbf{2}$ 生成的极限，终对象可以看成空范畴 $\mathbf{0}$（而非 $\mathbf{1}$）生成的极限（缩称唯一顶点，并且其它点到极限都有态射）。

类似的，余极限对应了余积和始对象。

### 等化子

> **等化子**（Equalizer）是由一个 $\mathbf{2}$ 生成的极限 $\varprojlim(F)$，其中的两个对象上有平行态射（以及恒等态射），使下图交换：
>
> ![Equalizer](/img/in-post/post-algebra/equalizer.svg){:height="250px" width="250px"}
>
> 从交换图可以看出满足 $f \circ p = g \circ p$。

当 $\mathcal{C}$ 是一个 Set 范畴的时候，函数 $p$ 是集合间的映射，因此 $p$ 的像是 $D\_A$ 的子集。在这个子集上，$f = g$。即方程 $f(x) = g(x)$ 的解 $x \in \varprojlim(F)$。

> **举例** 取 $D\_A$ 为参数化的二维平面 $(x, y)$，$D\_B$ 为直线。令 $f (x, y) = 2 y + x, g (x, y) = y - x$。
>
> 则等化子 $C$ 为满足 $f(x, y) = g(x, y)$ 的实数集（一条直线），函数 $p\ t = (t, -2 t)$。
>
> 对于其它锥形 $C'$，可以规约到泛锥。例如取 $() \in \mathbf{1}$ 作为 $C'$，函数 $p'\ () = (0, 0)$。它满足 $f (0, 0) = g (0, 0)$，但是存在 $h\ () = 0$ 来将其规约到 $C$。

### 拉回

> 设 $\mathcal{I}$ 为形如 $\cdot \rightarrow \cdot \leftarrow \cdot$ 的范畴，设 $\beta : \mathcal{I} \rightarrow \mathcal{C}$ 对应到 $\mathcal{C}$ 中的交换图 $X \rightarrow Z \leftarrow Y$。记 $X \underset{Z}{\times} Y = \underset{\leftarrow}{\operatorname{\mathrm{lim}}} \beta$，称为 $X \rightarrow Z$ 和 $Y \rightarrow Z$ 的**纤维积**（fibre product）或**拉回**（pullback）。
>
> ![Pullback](/img/in-post/post-algebra/pullback.svg){:height="250px" width="250px"}
>
> 拉回也可以用 $\Box$ 标记：
>
> ![Pullback 2](/img/in-post/post-algebra/pullback-2.svg){:height="200px" width="200px"}

此处 $X \underset{Z}{\times} Y \rightarrow Z$ 不用标出，因为根据态射的传递性，一定有 $f \circ p = g \circ q : X \underset{Z}{\times} Y \rightarrow Z$。

> **举例** 拉回在 C++ 中也有体现：将类作为对象，如果子类继承了父类，那么它们之间有一个态射；并且假设每个类都继承了子集（恒等态射），此时继承关系构成了一个范畴。
>
> 在 C++ 中支持多继承，因此会出现菱形继承：例如在上面的交换图中 $X$ 和 $Y$ 都是 $Z$ 的子类，而 $X \underset{Z}{\times} Y$ 同时继承了 $X$ 和 $Y$。在继承关系中，拉回 $X \underset{Z}{\times} Y$ 是“最简单”的继承关系，即没有新的数据字段或方法。
>
> 在上面的交换图中，$C'$ 继承了 $X$ 和 $Y$，但是没有直接继承拉回。但是根据拉回的定义可知，$C'$ 可以隐式转换到拉回 $X \underset{Z}{\times} Y$（尽管编译器无法推断出这个关系）。

> **举例** 拉回可以用于类型推断。
>
> 假设需要推断语句 `twice f x = f (f x)` 的类型。首先给所有变量和子表达式赋初始类型：
> ```
> f       :: t0
> x       :: t1
> f x     :: t2
> f (f x) :: t3
> ```
>
> 因此得到 `twice :: t0 -> t1 -> t3`。
>
> 根据函数应用的规则有
>
> ```
> t0 = t1 -> t2   -- f x
> t0 = t2 -> t3   -- f (f x)
> ```
>
> 这里需要解出这个代换，使得其形式最简因而签名最通用，得到的就是拉回。

### 推出

推出是拉回的对偶。

> 设 $\mathcal{I}$ 为形如 $\cdot \leftarrow \cdot \rightarrow \cdot$ 的范畴，设 $\alpha : \mathcal{I} \rightarrow \mathcal{C}$ 对应到 $\mathcal{C}$ 中的交换图 $X \leftarrow Z \rightarrow Y$。记 $X \underset{Z}{\sqcup} Y = \underset{\rightarrow}{\operatorname{\mathrm{lim}}} \alpha$，称为 $Z \rightarrow X$ 和 $Z \rightarrow Y$ 的**纤维余积**（fibre coproduct）或**拉回**（pushout）。
>
> ![Pushout](/img/in-post/post-algebra/pushout.svg){:height="250px" width="250px"}
>
> 拉回也可以用 $\boxplus$ 标记：
>
> ![Pushout 2](/img/in-post/post-algebra/pushout-2.svg){:height="200px" width="200px"}

## 连续函子

普通函子能够保持原范畴的态射和交换图，因此每个函子都是几乎连续的。但是函子无法保持极限的唯一性条件（$C'$ 到 $C$ 有唯一的态射）。能够保持极限的函子称为**连续函子**（continuous functor）。

Hom 函子就是一个连续函子。下面以 Haskell 为例介绍它是如何保持极限的。Hom 函子 $\operatorname{\mathrm{Hom}}\_{\mathcal{C}}(-, -)$ 的第一个参数是逆变的，第二个参数是协变的。因此保持第二个参数时，第一个参数会将余极限映射为极限；反之，保持第一个参数，可以将极限映射为极限。

在 Haskell 中，Hom 函子就是两个类型间的映射，因此可以用函数类型来表示。

> **逆变连续 Hom 函子** 保持第二个参数
>
> ```haskell
> newtype ToSring a = ToString (a -> String)
> instance Contravariant ToString where
>   contramap f (ToString g) = ToString (g. f)
> ```
>
> 取余积 `Either b c` 作为余极限，有下面的结论：
>
> ```haskell
> ToString (Either b c) ~ (b -> String, c -> String)
> ```

> **协变连续 Hom 函子** 保持第一个参数
>
> 即函数 `r -> a`，它保持极限是显然的。取类型积作为极限：
>
> ```haskell
> r -> (a, b) ~ (r -> a, r -> b)
> ```
