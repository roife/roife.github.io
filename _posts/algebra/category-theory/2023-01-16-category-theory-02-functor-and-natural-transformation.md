---
layout: "post"
title: "「范畴论」02 函子"
subtitle: "Functor"
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

> 设 $\mathcal{C}$ 与 $\mathcal{D}$ 为范畴，则函子 $F : \mathcal{C} \rightarrow \mathcal{D}$ 会把 $\mathcal{C}$ 中的所有**对象**与**态射**嵌入到 $\mathcal{D}$ 上，并保持范畴的结构（恒等映射与态射复合）：
>
> - 对象映射 $F : \operatorname{\mathrm{Ob}}(\mathcal{C}) \rightarrow \operatorname{\mathrm{Ob}}(\mathcal{D})$，即 $x : \mathcal{C} \mapsto FX : \mathcal{D}$
> - 态射映射 $F : \mathcal{C}(X, Y) \rightarrow \mathcal{D}(FX, FY)$
> - 保持恒等映射 $F(\mathbf{1}\_A) = \mathbf{1}\_{F(A)}$
> - 保持态射复合 $F(g \circ_\mathcal{C} f) = F(g) \circ_\mathcal{D} F(f)$

![Covariant Functor](/img/in-post/post-algebra/covariant-functor.svg){:height="400px" width="400px"}

在 Haskell 中，则表现为：

```haskell
fmap id = id
fmap (g . f) = (fmap g) . (fmap f)
```

函子是小范畴范畴（Cat 范畴）上的态射，其对象为小范畴，且存在恒等函子和函子复合。

# 函子的性质

对于函子 $F : \mathcal{C} \rightarrow \mathcal{D}$：
- 若 $\mathcal{D}$ 中任一对象都同构于某个 $FX\ (X \in \operatorname{\mathrm{Ob}}(\mathcal{C}))$，则称 $F$ 是**本质满的**（essentially surjective on objects，e.s.o.）
- 若对所有 $X, Y \in \operatorname{\mathrm{Ob}}(\mathcal{C})$，映射 $\mathcal{C}(X, Y) \rightarrow \mathcal{D}(FX,FY)$ 都是单射，则称函子 $F$ 是**忠实的**（faithful）
- 若对所有 $X, Y \in \operatorname{\mathrm{Ob}}(\mathcal{C})$，映射 $\mathcal{C}(X, Y) \rightarrow \mathcal{D}(FX,FY)$ 都是满射，则称函子 $F$ 是**全的**（full）

# Haskell 中的函子定义

Haskell 中函子的定义如下：

```haskell
class Functor f where
  fmap :: (a -> b) -> (f a -> B)
```

其中，`a -> b` 中的箭头为 $\mathcal{C}$ 上的态射，`f a -> f b` 中的箭头为 $\mathcal{D}$ 上的态射。而中间的箭头则表示两个范畴间的态射，和另外两个箭头是不一样的含义。

### 扩展的定义

实际上，范畴中的态射也可以不是函数映射：

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

-- Functor :: (k1 -> k) -> Constraint
-- CategoricalFunctor :: (k1 -> k) -> (k1 -> k1 -> *) -> (k -> k -> *) -> Constraint
```

# 共变函子（反函子）与反变函子

对于函子 $F : \mathcal{C} \rightarrow \mathcal{D}$，它在反范畴上对应的函子 $F^{\mathrm{op}} : \mathcal{C}^{\mathrm{op}} \rightarrow \mathcal{D}^{\mathrm{op}}$。$F^{\mathrm{op}}$ 在 Haskell 中的定义如下：

```haskell
class Functor f where
  fmap :: (b ~> a) -> (f b ~> f a)
```

不难发现 $F = F^{\mathrm{op}}$，函子 $F^{\mathrm{op}}$ 也称为**共变函子**（covariant functor），即通常说的函子。一般所说的反函子（opposite functor）也是指共变函子 $F^{\mathrm{op}} : \mathcal{C}^{\mathrm{op}} \rightarrow \mathcal{D}^{\mathrm{op}}$。

与之对偶的是**反变函子**（contravariant functor）$F' : \mathcal{C}^{\mathrm{op}} \rightarrow \mathcal{D}$（或 $F^{\mathrm{op}}' : \mathcal{C} \rightarrow \mathcal{D}^{\mathrm{op}}$）：
- 对象映射 $F' : \operatorname{\mathrm{Ob}}(\mathcal{C}) \rightarrow \operatorname{\mathrm{Ob}}(\mathcal{D})$（或 $F' : \operatorname{\mathrm{Ob}}(\mathcal{C}^{\mathrm{op}}) \rightarrow \operatorname{\mathrm{Ob}}(D)$）
- 态射映射 $F' : \mathcal{C}(X, Y) \rightarrow \mathcal{D}(FY, FX)$
- 保持单位态射
- 态射复合 $F'(g \circ\_\mathcal{C^{\mathrm{op}}} f) = F'(g) \circ\_\mathcal{D} F'(f)$

```haskell
class Contravariant f where
  contramap ::(b ~> a) -> (f a ~> f b)
```

![Cotravariant Functor](/img/in-post/post-algebra/contravariant-functor.svg){:height="350px" width="350px"}

一般会将反变函子称为 cofunctor。

# 二元函子

（共变）二元函子（Bifunctor） $F : \mathcal{C} \times \mathcal{D} \rightarrow \mathcal{E}$ 能将两个范畴的笛卡尔积映射到新范畴。显然，二元函子满足函子的定义：
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

而对应的反变二元函子 $F : \mathcal{C}^{\mathrm{op}} \times \mathcal{D} \rightarrow \mathcal{E}$ 称为 Profunctor。

```haskell
class Profunctor p where
  dimap :: (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g
  lmap :: (a -> b) -> p b c -> p a c
  lmap f = dimap f id
  rmap :: (b -> c) -> p a b -> p a c
  rmap = dimap id
```

# Hom 函子

局部小范畴 $\mathcal{C}$ 上所有的 Hom 集组成的集合组成 了一个 Set 范畴（集合范畴的子范畴），范畴 $\mathcal{C}$ 到这个 Set 范畴的映射即为共变 Hom 函子，而反范畴 $\mathcal{C}^{\mathrm{op}}$ 到这个 Set 范畴的映射即为反变 Hom 函子。

> 给定局部小范畴 $\mathcal{C}$，**共变 Hom 函子**（covariant Hom-functor）$\operatorname{\mathrm{Hom}}(A, -) : \mathcal{C} \rightarrow \mathtt{Set}$ 的定义如下：
> - $\forall B \in \operatorname{\mathrm{Ob}}(\mathcal{C}),\  \operatorname{\mathrm{Hom}}(A, -)(B) = \operatorname{\mathrm{Hom}}(A, B)$
> - $\forall f : B \rightarrow C \in \operatorname{\mathrm{Arr}}(\mathcal{C}),\  \operatorname{\mathrm{Hom}}(A, -)(f) = \operatorname{\mathrm{Hom}}(A, f) : \operatorname{\mathrm{Hom}}(A, B) \rightarrow \operatorname{\mathrm{Hom}}(A, C)$
>   + $\operatorname{\mathrm{Hom}}(A, f)(g : A \rightarrow B) = f \circ g : A \rightarrow C$

在 Haskell 中的对应表述为：

```haskell
instance Functor ((->) a) where
  fmap f g = (f . g)
```

> 给定局部小范畴 $\mathcal{C}$，**反变 Hom 函子**（contravariant Hom-functor）$\operatorname{\mathrm{Hom}}(-, B) : \mathcal{C}^{\mathrm{op}} \rightarrow \mathtt{Set}$ 的定义如下：
> - $\forall B \in \operatorname{\mathrm{Ob}}(\mathcal{C}),\  \operatorname{\mathrm{Hom}}(-, A)(B) = \operatorname{\mathrm{Hom}}(B, A)$
> - $\forall h : C \rightarrow B \in \operatorname{\mathrm{Arr}}(\mathcal{C}),\  \operatorname{\mathrm{Hom}}(-, A)(h) = \operatorname{\mathrm{Hom}}(h, A) : \operatorname{\mathrm{Hom}}(B, A) \rightarrow \operatorname{\mathrm{Hom}}(C, A)$
>   + $\operatorname{\mathrm{Hom}}(h, A)(g : B \rightarrow A) = g \circ h : C \rightarrow A$

在 Haskell 中的对应表述为：

```haskell
data Op b a = Op (a -> b)
instance Contravariant (Op a) where
  contramap h (Op g) = Op (g . h)
```

![Hom Functor](/img/in-post/post-algebra/hom-functor.svg){:height="400px" width="400px"}

下面给出共变 Hom 函子的证明：

- $\operatorname{\mathrm{Hom}}(A, \operatorname{\mathrm{id}}\_X)(f) = \operatorname{\mathrm{id}}\_X \circ f = f$，因此 $\operatorname{\mathrm{Hom}}(A, \operatorname{\mathrm{id}}\_X) = \operatorname{\mathrm{id}}\_{\operatorname{\mathrm{Hom}}(A, X)}$
- $\operatorname{\mathrm{Hom}}(A, g \circ f)(h) = g \circ f \circ h = (\operatorname{\mathrm{Hom}}(A, g) \circ \operatorname{\mathrm{Hom}}(A, f))(h)$，因此 $\operatorname{\mathrm{Hom}}(A, g \circ f) = \operatorname{\mathrm{Hom}}(A, g) \circ \operatorname{\mathrm{Hom}}(A, f)$

此外，还可以定义二元函子：

> 二元函子 $\operatorname{\mathrm{Hom}}(-, -) : \mathcal{C}^{\mathrm{op}} \times \mathcal{C} \rightarrow \mathtt{Set}$ 的定义如下：
> - $\forall f : B \rightarrow B'\ \forall h : A' \rightarrow A,\ \operatorname{\mathrm{Hom}}(h, f) : \operatorname{\mathrm{Hom}}(A, B) \rightarrow \operatorname{\mathrm{Hom}}(A', B')$
>   + 它使得 $g : A \rightarrow B \mapsto f \circ g \circ h : A' \rightarrow B'$


# 函子的复合

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
- 复合的结果 $G \circ F$ 也是函子（`f <$> G (F x) = G (F (f x))`）
- 存在单位函子 $\operatorname{\mathrm{id}}$，对于 $F : \mathcal{A} \rightarrow \mathcal{B}$，有 $F \circ \operatorname{\mathrm{id}}\_{\mathcal{A}} = \operatorname{\mathrm{id}}\_{\mathcal{B}} \circ F = F$
- 函子的复合运算 $\circ$ 满足结合律，即对于函子 $F, G, H$，满足 $(H \circ G) \circ F = H \circ (G \circ F)$
