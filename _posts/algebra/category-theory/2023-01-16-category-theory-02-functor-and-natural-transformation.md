---
layout: "post"
title: "「范畴论」02 函子与自然变换"
subtitle: "Functor and Natural transformation"
author: "roife"
date: 2023-01-16

tags: ["代数@数学", "数学@Tags", "Haskell@编程语言", "范畴论@数学"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 函子

## 函子的定义

前面关注的都是对象间的态射，下面关注范畴（小范畴）间的态射——**函子**（functor）。
由于函子也是态射，因此也满足态射的定律。

函子的定义如下：

> 设 $\mathcal{C}$ 与 $\mathcal{D}$ 为范畴，则函子 $F : \mathcal{C} \rightarrow \mathcal{D}$ 会把 $\mathcal{C}$ 中的所有**对象**与**态射**对应到 $\mathcal{D}$ 上，且保留**复合运算**与**单位元**（恒等映射）：
>
> - $F(f : A \rightarrow B) = F(f) : F(A) \rightarrow F(B)$
> - $F(\mathbf{1}\_A) = \mathbf{1}\_{F(A)}$
> - $F(g \circ_\mathcal{C} f) = F(g) \circ_\mathcal{D} F(f)$

![Covariant Functor](/img/in-post/post-algebra/covariant-functor.svg){:height="400px" width="400px"}

在 Haskell 中，则表现为：

```haskell
fmap id = id
fmap (g . f) = (fmap g) . (fmap f)
```

如果函子 $F, G : \mathcal{C} \rightarrow \mathcal{D}$ 都是从 $\mathcal{C}$ 到 $\mathcal{D}$ 的态射，那么称这两个函子为**平行函子**（parallel functor）。

## 函子的性质

对于函子 $F : \mathcal{C} \rightarrow \mathcal{D}$：
- 若 $\mathcal{D}$ 中任一对象都同构于某个 $FX\ (X \in \operatorname{\mathrm{Ob}}(\mathcal{C}))$，则称 $F$ 是**本质满的**（essentially surjective on objects，e.s.o.）
- 若对所有 $X, Y \in \operatorname{\mathrm{Ob}}(\mathcal{C})$，映射 $\operatorname{\mathrm{Hom}}\_{\mathcal{C}}(X, Y) \rightarrow \operatorname{\mathrm{Hom}}\_{\mathcal{D}}(FX,FY)$ 都是单射，则称函子 $F$ 是**忠实的**（faithful）
- 若对所有 $X, Y \in \operatorname{\mathrm{Ob}}(\mathcal{C})$，映射 $\operatorname{\mathrm{Hom}}\_{\mathcal{C}}(X, Y) \rightarrow \operatorname{\mathrm{Hom}}\_{\mathcal{D}}(FX,FY)$ 都是满射，则称函子 $F$ 是**全的**（full）

## Haskell 中的函子定义

Haskell 中函子的定义如下：

```haskell
class Functor f where
  fmap :: (a -> b) -> (f a -> B)
```

其中，`a -> b` 中的箭头为 $\mathcal{C}$ 上的态射，`f a -> f b` 中的箭头为 $\mathcal{D}$ 上的态射。而中间的箭头则表示两个范畴间的态射，和另外两个箭头是不一样的含义。

### 二元函子

二元函子 $F : \mathcal{C} \times \mathcal{D} \rightarrow \mathcal{E}$ 能将两个范畴的笛卡尔积映射到新范畴。显然，二元函子满足函子的定义：
- 单位元为 $(\operatorname{\mathrm{id}}\_{\mathcal{C}}, \operatorname{\mathrm{id}}\_{\mathcal{D}})$
- 复合运算 $(f, g) \circ (f', g') = (f \circ f', g \circ g')$

二元函子在 Haskell 中的定义如下：

```haskell
class Bifunctor f where
    bimap :: (a -> c) -> (b -> d) -> f a b -> f c d
    bimap g h = first g . second h
    first :: (a -> c) -> f a b -> f c b
    first g = bimap g id
    second :: (b -> d) -> f a b -> f a d
    second = bimap id
```

### 扩展的定义

范畴中的态射也可以不是函数映射：

```haskell
class (Category r, Category t) =>
        CategoricalFunctor f (r :: i -> i -> *) (t :: j -> j -> *)
        | f r -> t, f t -> r where
  cfmap :: r a b -> t (f a) (f b)

instance CategoricalFunctor Maybe (->) (->) where
  cfmap f Nothing  = Nothing
  cfmap f (Just a) = Just (f a)
```

此外，`f` 的 kind 不一定是 `* -> *` 可以是 `k -> k1`。可以借助 type family 让 Haskell 区分 `->` 与 `~>`（令 `->` 为函子的映射，`~>` 为范畴内的态射）：

```haskell
type family (~>) :: k -> k1 -> *

type instance (~>) = (->)
class Category cat where
  id :: cat a a
  (.) :: cat b c -> cat a b -> cat a c

-- 更严格的定义为 class (cat ~ (~>)) => Category cat where
-- 来指定对象间的态射为(~>)，但是由于类型系统的限制，这样定义会导致有 2 个
-- 以上类型参数的类型无法定义为范畴类型类的实例。

type Hask = (->)
instance Category Hask where
  id x = x
  (.) g f x = g (f x)

class Functor f where
  fmap :: (a ~> b) -> (f a ~> f b)

class (Category r, Category t) =>
        CategoricalFunctor f r t | f r -> t, f t -> r where
  cfmap :: r a b -> t (f a) (f b)

-- > :k Functor
-- Functor :: (k1 -> k) -> Constraint

-- > :k CategoricalFunctor
-- CategoricalFunctor :: (k1 -> k) -> (k1 -> k1 -> *) -> (k -> k -> *) -> Constraint
```

## 共变函子与反变函子

对于函子 $F : \mathcal{C} \rightarrow \mathcal{D}$，它在反范畴上对应的函子 $G : \mathcal{C}^{\mathrm{op}} \rightarrow \mathcal{D}^{\mathrm{op}}$。$G$ 的定义如下：

```haskell
class Functor f where
  fmap :: (b ~> a) -> (f b ~> f a)
```

不难发现 $F = G$，函子 $G$ 也称为**共变函子**（covariant functor），本质上就是函子。

与之对偶的是反变函子（contravariant functor）$F' : \mathcal{C}^{\mathrm{op}} \rightarrow \mathcal{D}$（或 $G' : \mathcal{C} \rightarrow \mathcal{D}^{\mathrm{op}}$）：

```haskell
class Contravariant f where
  contramap ::(b ~> a) -> (f a ~> f b)
```

![Cotravariant Functor](/img/in-post/post-algebra/contravariant-functor.svg){:height="400px" width="400px"}

一般会将反变函子称为 cofunctor。

## Hom 函子

范畴 $\mathcal{C}$ 上所有的 `Hom-Set` 组成的集合组成了一个 Set 范畴，范畴 $\mathcal{C}$ 到这个 Set 范畴的映射即为共变 Hom 函子，而反范畴 $\mathcal{C}^{\mathrm{op}}$ 到这个 Set 范畴的映射即为反变 Hom 函子。

> 给定局部小范畴 $\mathcal{C}$，**共变 Hom 函子**（covariant Hom-functor）$\operatorname{\mathrm{Hom}}(A, -) : \mathcal{C} \rightarrow \mathtt{Set}$ 的定义如下：
> - $\forall B \in \operatorname{\mathrm{Ob}}(\mathcal{C}),\  \operatorname{\mathrm{Hom}}(A, -)(B) = \operatorname{\mathrm{Hom}}(A, B)$
> - $\forall f : B \rightarrow C \in \operatorname{\mathrm{Arr}}(\mathcal{C}),\  \operatorname{\mathrm{Hom}}(A, -)(f) = \operatorname{\mathrm{Hom}}(A, f) : \operatorname{\mathrm{Hom}}(A, B) \rightarrow \operatorname{\mathrm{Hom}}(A, C)$
>   + 它使得 $g : A \rightarrow B \mapsto f \circ g : A \rightarrow C$

在 Haskell 中的对应表述为：

```haskell
instance Functor ((->) a) where
  fmap f g = (f . g)
```

> 给定局部小范畴 $\mathcal{C}$，**反变 Hom 函子**（contravariant Hom-functor）$\operatorname{\mathrm{Hom}}(-, B) : \mathcal{C}^{\mathrm{op}} \rightarrow \mathtt{Set}$ 的定义如下：
> - $\forall B \in \operatorname{\mathrm{Ob}}(\mathcal{C}),\  \operatorname{\mathrm{Hom}}(-, A)(B) = \operatorname{\mathrm{Hom}}(B, A)$
> - $\forall h : C \rightarrow B \in \operatorname{\mathrm{Arr}}(\mathcal{C}),\  \operatorname{\mathrm{Hom}}(-, A)(h) = \operatorname{\mathrm{Hom}}(h, A) : \operatorname{\mathrm{Hom}}(B, A) \rightarrow \operatorname{\mathrm{Hom}}(C, A)$
>   + 它使得 $g : B \rightarrow A \mapsto g \circ h : C \rightarrow A$

在 Haskell 中的对应表述为：

```haskell
data Op b a = Op (a -> b)
instance Contravariant (Op a) where
  contramap h (Op g) = Op (g . h)
```

![Hom Functor](/img/in-post/post-algebra/hom-functor.svg){:height="400px" width="400px"}

> 二元函子 $\operatorname{\mathrm{Hom}}(-, -) : \mathcal{C}^{\mathrm{op}} \times \mathcal{C} \rightarrow \mathtt{Set}$ 被称为**Hom 函子**（Hom-functor），其定义如下：
> - $\forall f : B \rightarrow B'\ \forall h : A' \rightarrow A,\ \operatorname{\mathrm{Hom}}(h, f) : \operatorname{\mathrm{Hom}}(A, B) \rightarrow \operatorname{\mathrm{Hom}}(A', B')$
>   + 它使得 $g : A \rightarrow B \mapsto f \circ g \circ h : A' \rightarrow B'$

## 函子的复合

函子的复合实际上是类型的复合。在 Haskell 中，函子的复合定义在 `Data.Functor.Compose` 中和 `GHC.Generics` 中，`:.:` 可以进行类型的复合。

```haskell
newtype Compose f g a = Compose { getCompose :: f (g a) } -- Data.Functor.Compose
newtype (:.:) f g p = Comp1 { unComp1 :: f (g p) } -- GHC.Generics
-- p :: f (g p)

-- > :k (:.:)
-- (:.:) :: (k1 -> *) -> (k -> k1) -> k -> *

-- > :t (.)
-- (.) :: (b -> c) -> (a -> b) -> a -> c
```

设范畴 $\mathcal{A}, \mathcal{B}, \mathcal{C}$，对于函子 $F : \mathcal{A} \rightarrow \mathcal{B},\ G : \mathcal{B} \rightarrow \mathcal{C}$，它们的复合 $G \circ F : \mathcal{A} \rightarrow \mathcal{C}$ 满足下面的性质：
- 对于任意函子 $F : \mathcal{A} \rightarrow \mathcal{B}$，有 $F \circ \operatorname{\mathrm{id}}\_{\mathcal{A}} = \operatorname{\mathrm{id}}\_{\mathcal{B}} \circ F = F$，其中 $\operatorname{\mathrm{id}}\_{\mathcal{A}}$ 为 $\mathcal{A}$ 上的单位函子
- 复合的结果 $G \circ F$ 也是函子（`f <$> G (F x) = G (F (f x))`）
- 函子的复合运算 $\circ$ 满足结合律，即对于函子 $F, G, H$，满足 $(H \circ G) \circ F = H \circ (G \circ F)$

# 自然变换

## 自然变换的定义

**自然变换**（natural transformation）是函子之间的态射，$F$ 到 $G$ 的自然态射也可以记作 $\operatorname{\mathrm{Nat}}(F, G)$。

> 设范畴 $\mathcal{C}, \mathcal{D}$ 间的函子 $F, G : C \rightarrow D$，自然变换 $\theta_X : FX \rightarrow GX$ 是 $\mathcal{D}$ 上的一组态射：
>
> $$
> \theta_X \in \operatorname{\mathrm{Hom}}_{\mathcal{D}}(FX, GX), X \in \operatorname{\mathrm{Ob}}(C)
> $$
>
> 使得对于 $\mathcal{C}$ 上的所有态射 $f : X \rightarrow Y$，下图交换：
>
> ![Natural Transformation](/img/in-post/post-algebra/natural-transformation.svg){:height="250px" width="250px"}
>
> 上面这幅图也可以记作：
>
> ![Natural Transformation 2](/img/in-post/post-algebra/natural-transformation-2.svg){:height="250px" width="250px"}
>
> 即满足 $\theta_X \circ Gf = Ff \circ \theta_Y$，称 $\theta$ 是 natural 的（或满足 naturality）。

## Haskell 中的自然变换

```haskell
newtype Nat f g = Nat {runNat :: forall a. f a ~> g a}

-- > :k Nat
-- Nat :: (k2 -> k) -> (k2 -> k1) -> *
```

Haskell 中的自然变换非常常见，例如：

```haskell
reverse :: [a] -> [a]    -- 自然同构，且 F = G
return  :: a -> [a]      -- Identity a -> [a]
concat  :: [[a]] -> [a]
flatten :: Tree a -> [a]
```

使用函子进行映射（$F f$）会改变容器内的“值”，而不会改变容器的结构；而自然变换可能会改变结构。

由交换图知自然变换 $\theta$ 满足对任意的 $f$，$\theta \circ \operatorname{\mathrm{fmap}}\ f = \operatorname{\mathrm{fmap}}\ f \circ \theta$，$\theta \circ \operatorname{\mathrm{contramap}}\ f = \operatorname{\mathrm{contramap}}\ f \circ \theta$）

## 自然变换的合成

自然变换有两种合成方式：横合成和纵合成。并且横纵合成的结构都是函子范畴上的态射，满足结合律 $(\phi \circ \psi) \circ \theta = \phi \circ (\psi \circ \theta)$。

### 纵合成

考虑范畴 $\mathcal{C}, \mathcal{D}$ 间的三个函子 $F, G, H$ 以及自然变换 $\theta : F \rightarrow G,\ \psi : G \rightarrow H$，**纵合成**（vertical composition）$(\psi \circ \theta)_X = \psi_X \circ \theta_X\ (X \in \operatorname{\mathrm{Ob}}(\mathcal{C}))$。

![Vertical Composition](/img/in-post/post-algebra/vertical-composition.svg){:height="600px" width="600px"}

```haskell
verticalComp :: (Functor f , Functor g, Functor (h :: k -> *))
             => Nat f g -> Nat g h -> Nat f h
verticalComp theta@(Nat fg) psi@(Nat gh) = Nat $ gh . fg
```

> **证明** 纵合成是自然变换
>
> 设自然变换 $\theta : F \rightarrow G,\ \psi : G \rightarrow H$，则下面的交换图成立：
>
> $$
> \begin{CD}
> FX @>\theta_X>> GX   @.  GX @>\psi_X>> HX     \\
> @VFfVV        @VVGfV  @VGfVV        @VVHfV  \\
> FY @>>\theta_Y> GY   @.  GY @>>\psi_B> HY
> \end{CD}
> $$
>
> 两幅交换图可以拼成一张，得到：
>
> $$
> \begin{CD}
> FX @>(\psi \circ \theta)_X>> HX    \\
> @VFfVV        @VVHfV  \\
> FY @>>(\psi \circ \theta)_Y> HY
> \end{CD}
> $$
>
> 则纵合成是自然变换。

### 横合成

考虑范畴 $\mathcal{C}, \mathcal{D}, \mathcal{E}$ 间的四个函子 $F_1, F_2, G_1, G_2$ 以及自然变换 $\theta : F_1 \rightarrow F_2,\ \psi : G_1 \rightarrow G_2$，**横合成**（horizontal composition）$(\psi \circ \theta)_X : (G_1 \circ F_1) X \rightarrow (G_2 \circ F_2) X\ (X \in \operatorname{\mathrm{Ob}}(\mathcal{C}))$。

$(\psi \circ \theta)_X$ 对应了下面的交换图：

![Horizontal Commutative](/img/in-post/post-algebra/horizontal-commutative.svg){:height="300px" width="300px"}

![Horizontal Composition](/img/in-post/post-algebra/horizontal-composition.svg){:height="700px" width="700px"}

```haskell
horizontalComp :: (Functor f1, Functor f2, Functor g1, Functor g2) =>
  Nat f1 f2 -> Nat g1 g2 -> Nat (g1 :.: f1) (g2 :.: f2)
  -- f1f2      :: f1 a -> f2 a
  -- g1g2      :: g1 a -> g2 a
  -- x         :: g1 (f1 a)
  -- g1g2 x    :: g2 (f1 a)
  -- fmap f1f2 :: g2 (f2 a)
horizontalComp theta@(Nat f1f2) psi@(Nat g1g2) = Nat $ \(Comp1 x) -> Comp1 (fmap f1f2 (g1g2 x))
```

横合成本质上只是函子的复合。

> **证明** 横合成是自然变换
>
> 对于上面的定义，可以得到交换图：
>
> $$
> \begin{CD}
> (G_1 \circ F_1)X @>G_1 \theta_X>> (G_1 \circ F_2)X @>\psi_{F_2 X}>> (G_2 \circ F_2)X  \\
> @VG_1 F_1 fVV                    @VG_1 F_2 fVV                       @VVG_2 F_2 fV \\
> (G_1 \circ F_1)Y @>>G_1 \theta_Y> (G_1 \circ F_2)Y @>>\psi_{F_2 Y}> (G_2 \circ F_2)Y
> \end{CD}
> $$

此外，横合成还有一类特殊情况，即函子和自然变换的合成：

![Horizontal Composition-2](/img/in-post/post-algebra/horizontal-composition-2.svg){:height="300px" width="300px"}

- $\theta H : FH \rightarrow GH$ 可以看成 $\theta$ 和 $\operatorname{\mathrm{id}}\_H : H \rightarrow H$ 的复合，简记为 $\theta \circ \operatorname{\mathrm{id}}_H$
  + $(\theta \circ H)\_X = \theta\_{HX} : (F \circ H)X \rightarrow (G \circ H)X$

```haskell
preFComp :: (Functor f, Functor g, Functor h)
         => Nat g h -> g (f a) -> h (f a)
preFComp (Nat gh) fa = gh fa
```

- $K \theta : KF \rightarrow KG$ 可以看成 $\theta$ 和 $\operatorname{\mathrm{id}}\_K : K \rightarrow K$ 的复合，简记为 $\operatorname{\mathrm{id}}\_K \circ \theta$
  + $(K \circ \theta)\_X = K(\theta\_{X}) : (K \circ F)X \rightarrow (K \circ G)X$

```haskell
postFComp :: (Functor f, Functor g, Functor h)
          => Nat g h -> f (g a) -> f (h a)
postFComp (Nat gh) fa = fmap gh fa
```

### 横纵合成互换定律

![Vertical-Horizontal Composition](/img/in-post/post-algebra/v-h-composition.svg){:height="400px" width="400px"}

对于上面的图表，存在互换律：

$$
(\psi_2 \circ \psi_1) \circ (\theta_2 \circ \theta_1) = (\psi_2 \circ \theta_2) \circ (\psi_1 \circ \theta_1)
$$

其中不同位置的 $\circ$ 代表不同的横纵合成。

## 自然变换的逆与自然同构

给定范畴 $\mathcal{C}, \mathcal{D}$，对于函子 $F : \mathcal{C} \rightarrow \mathcal{D},\ G : \mathcal{D} \rightarrow \mathcal{C}$，给定自然变换 $\theta : F \rightarrow G$，若 $\psi : G \rightarrow F$ 满足 $\psi \circ \theta = \operatorname{\mathrm{id}}\_F,\ \theta \circ \psi = \operatorname{\mathrm{id}}\_G$，则称自然变换 $\psi$ 是 $\theta$ 的**逆**，记作 $\theta^{-1}$。

自然变换可逆称为它是**自然同构**（natural isomorphism），记作 $\theta : F \overset{\sim}{\rightarrow} G$，并称函子 $F$ 与 $G$ 同构。易得 $(\theta^{-1})\_X = (\theta\_X)^{-1} : G X \overset{\sim}{\rightarrow} F X$。

## 拟逆函子与范畴等价

若存在函子间的同构 $\theta : FG \overset{\sim}{\rightarrow} \operatorname{\mathrm{id}}\_{\mathcal{D}}$，$\psi : GF \overset{\sim}{\rightarrow} \operatorname{\mathrm{id}}\_{\mathcal{C}}$，则称 $G$ 是 $F$ 的**拟逆函子**（quasi inverse），且 $F$ 是 $\mathcal{C}$ 到 $\mathcal{D}$ 的一个**等价**（equivalence）。

进一步的，若 $F G = \operatorname{\mathrm{id}}\_{\mathcal{D}}$ 且 $G F = \operatorname{\mathrm{id}}\_{\mathcal{C}}$，则称 $F$ 是一个 $\mathcal{C}$ 到 $\mathcal{D}$ 的**同构**，并称 $G$ 是 $F$ 的**逆**。

> **定理** 对于函子 $F : \mathcal{C} \rightarrow \mathcal{D}$，$F$ 是范畴等价当且仅当 $F$ 是全忠实、本质满函子（证明略）

## 函子范畴

自然变换可以看成**函子范畴**上的态射，函子范畴的对象为函子。此时原范畴上的自然同构变成了函子范畴上的同构态射。其严格定义如下：

> 设 $\mathcal{C}, \mathcal{D}$ 为小范畴，则函子范畴 $\operatorname{\mathrm{Fct}}(\mathcal{C}, \mathcal{D})$ 的对象是 $\mathcal{C} \rightarrow \mathcal{D}$ 的函子，任意两个对象 $F, G$ 间的态射是自然变换 $\theta : F \rightarrow G$，合成运算为自然变换的纵合成。

函子范畴在 Haskell 中的表述如下：

```haskell
type instance (~>) = Nat
instance Category ((~>) :: i -> i -> *)
         => Category (Nat :: (k1 -> i) -> (k1 -> i) -> *) where
  id = Nat id
  Nat f . Nat g = Nat (f . g)
```

## Applicative 变换

Applicative 是特殊的 functor，相比自然变换而言，applicative 的变换则需要满足更多性质：

```haskell
t :: (Applicative f, Applicative g) => f a -> g a
```

- `t (pure x) = pure x`，需要注意两边的 `pure` 是不同类型的
- `t (x <*> y) = t x <*> t y`

此外，`Traversable` 中的函数也需要满足一些性质：

- `traverse Identity = Identity`
- `t . traverse f = traverse (t . f)`
- `traverse (Compose . fmap (g . f)) = Compose . fmap (traverse g) . traverse f`：`traverse` 遍历的过程可以移动到复合结构的内部或者外部

对于 `sequenceA` 来说，需要满足的定律和 `traverse` 相同：

- `sequenceA . (fmap Identity) = Identity`
- `t . sequenceA = sequenceA . fmap t`
- `sequenceA . fmap Compose = Compose . fmap sequenceA . sequenceA`

# Typeclass 限定范畴

Haskell 中的 typeclass 限定关系（例如 `Ord a` 可以导出 `Eq a`）满足范畴的定义。其中对象为 typeclass，限定关系为态射。

`Dict` 用于包装一个 `kind` 为 `Constraint` 的 typeclass。下面定义了 `:-` 运算符表示一个 typeclass 可以导出另一个 typeclass。

```haskell
import GHC.Types (Constraint) -- GHC 8.0前Constraint在GHC.Prim中 ..

data Dict (p :: Constraint) where
  Dict :: p => Dict p

-- Eq :: * -> Constraint
-- forall a. Eq a :: Constraint
-- Dict (forall a. Eq a) :: *

-- Sub :: (p => Dict q) -> p :- q
newtype p :- q = Sub (p => Dict q)

-- Sub Dict :: Ord a :- Eq a 可以导出
-- Sub Dict :: Eq a :- Ord a 报错
```

对于一个 typeclass，单位态射 `a :- a` 是显然的。而 `:-` 的复合也是显然的：`Ord a :- Eq a` 且 `Eq a :- Eq [a]`，则 `Ord a :- Eq [a]`。

```haskell
(\\) :: p => ((q => r) -> (p :- q) -> r)
r \\ (Sub Dict) = r

trans :: (b :- c) -> (a :- b) -> (a :- c)
trans f g = Sub $ (Dict \\ f) \\ g

instance Category (:-) where
  id = Sub Dict  -- id :: a :- a
  (.) = trans
```

此外，`Dict` 可以定义成一个函子，可以映射 `Constraint -> Dict`：

```haskell
type instance (~>) = (:-)

instance Functor Dict where
  fmap :: (a :- b) -> Dict a ~> Dict b
  fmap p Dict = case p of Sub q -> q

unfmap :: (Dict a -> Dict b) -> a :- b
unfmap f = Sub (f Dict)
```

显然 `Dict` 是一个全忠实函子。

对于 typeclass 的限定，有两个比较特殊的对象：
- `()` 表示空限定，例如 `() => Eq Int`，任何 typeclass 都可以导出 `()`，它是范畴上的终极对象
- 对应的初始对象则可以导出任何 typeclass 限定
