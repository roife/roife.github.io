---
layout: "post"
title: "「范畴论」03 自然变换与函子范畴"
subtitle: "Natural transformation and Functor category"
author: "roife"
date: 2023-01-20

tags: ["代数@数学", "数学@Tags", "Haskell@编程语言", "范畴论@数学"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 自然变换

## 自然变换的定义

**自然变换**（natural transformation）是函子之间的态射，$F$ 到 $G$ 的自然态射也可以记作 $\operatorname{\mathrm{Nat}}(F, G)$。

> 设范畴 $\mathcal{C}, \mathcal{D}$ 间的函子 $F, G : C \rightarrow D$，自然变换 $\theta_X : FX \rightarrow GX$ 是 $\mathcal{D}$ 上的一组态射：
>
> $$
> \theta_X \in \operatorname{\mathrm{Hom}}_{\mathcal{D}}(FX, GX), X \in \operatorname{\mathrm{Ob}}(C)
> $$
>
> 使得对于 $\mathcal{C}$ 上的所有态射 $f : X \rightarrow Y$，下图交换（称为自然性，naturality）：
>
> ![Natural Transformation](/img/in-post/post-algebra/natural-transformation.svg){:height="300px" width="300px"}
>
> 即满足 $\forall f \in \mathcal{C}(X, Y), \theta\_Y \circ Ff = Gf \circ \theta\_X$。上面这幅图也可以记作：
>
> ![Natural Transformation 2](/img/in-post/post-algebra/natural-transformation-2.svg){:height="200px" width="200px"}

由于 $FA, GA \in \operatorname{\mathrm{Ob}}(\mathcal{D})$，那么很自然地，态射 $\theta\_A(FA) = FB$ 也应当属于 $\operatorname{\mathrm{Arr}}(\mathcal{D})$。所以自然变换的本质就是 $\mathcal{D}$ 内部分特殊的态射，因此两个函子间不一定存在自然变换，取决于态射。

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

由交换图知自然变换 $\theta$ 满足对任意的 $f$：
- $\theta \circ \operatorname{\mathrm{fmap}}\ f = \operatorname{\mathrm{fmap}}\ f \circ \theta$
- $\theta \circ \operatorname{\mathrm{contramap}}\ f = \operatorname{\mathrm{contramap}}\ f \circ \theta$）

即：切换容器与 `fmap` 的顺序无关。

## 反自然变换

设函子 $F, G : \mathcal{C} \rightarrow \mathcal{D}$，则在反范畴中对应的有反函子 $F^{\mathrm{op}}, G^{\mathrm{op}} : \mathcal{C}^{\mathrm{op}} \rightarrow \mathcal{D}^{\mathrm{op}}$。

前面提到，自然变换本质上是范畴上原有的态射。由于在 $\mathcal{C}^{\mathrm{op}}$ 中，所有的态射都被反转了，因此从 $FA$ 到 $GA$ 的自然变换 $\theta\_A$ 也被反转了，得到 $\theta\_A^{\mathrm{op}} : G^{\mathrm{op}}A \rightarrow F^{\mathrm{op}}A$。因此反自然变换（opposite natural transformation）：$\theta^{\mathrm{op}} : G^{\mathrm{op}} \rightarrow F^{\mathrm{op}}$。且 $(\theta^{\mathrm{op}})^{\mathrm{op}} = \theta$。

## 自然变换的合成

自然变换有两种合成方式：横合成和纵合成。

并且横纵合成的结构都是函子范畴上的态射，满足结合律 $(\phi \circ \psi) \circ \theta = \phi \circ (\psi \circ \theta)$。

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

横合成还有一类特殊情况，即函子和自然变换的“合成”：

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

## 自然同构

给定范畴 $\mathcal{C}, \mathcal{D}$，对于函子 $F : \mathcal{C} \rightarrow \mathcal{D},\ G : \mathcal{D} \rightarrow \mathcal{C}$，给定自然变换 $\theta : F \rightarrow G$，若 $\psi : G \rightarrow F$ 满足 $\psi \circ \theta = \operatorname{\mathrm{id}}\_F,\ \theta \circ \psi = \operatorname{\mathrm{id}}\_G$，则称自然变换 $\psi$ 是 $\theta$ 的**逆**，记作 $\theta^{-1}$。

自然变换可逆称为它是**自然同构**（natural isomorphism），记作 $\theta : F \overset{\sim}{\rightarrow} G$，并称函子 $F$ 与 $G$ 同构。易得 $(\theta^{-1})\_X = (\theta\_X)^{-1} : G X \overset{\sim}{\rightarrow} F X$。

## 拟逆函子与范畴等价

若存在函子间的同构 $\theta : FG \overset{\sim}{\rightarrow} \operatorname{\mathrm{id}}\_{\mathcal{D}}$，$\psi : GF \overset{\sim}{\rightarrow} \operatorname{\mathrm{id}}\_{\mathcal{C}}$，则称 $G$ 是 $F$ 的**拟逆函子**（quasi inverse），且 $F$ 是 $\mathcal{C}$ 到 $\mathcal{D}$ 的一个**等价**（equivalence）。

进一步的，若 $F G = \operatorname{\mathrm{id}}\_{\mathcal{D}}$ 且 $G F = \operatorname{\mathrm{id}}\_{\mathcal{C}}$，则称 $G$ 是 $F$ 的**逆**，并称 $F$ 是一个 $\mathcal{C}$ 到 $\mathcal{D}$ 的**同构**。

> **定理** 对于函子 $F : \mathcal{C} \rightarrow \mathcal{D}$，$F$ 是范畴等价当且仅当 $F$ 是全忠实、本质满函子（证明略）

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

# 函子范畴

## 函子范畴

自然变换可以看成**函子范畴**上的态射，函子范畴的对象为函子。此时原范畴上的自然同构变成了函子范畴上的同构态射。其严格定义如下：

> 设 $\mathcal{C}, \mathcal{D}$ 为小范畴，记函子范畴为 $\operatorname{\mathrm{Fct}}(\mathcal{C}, \mathcal{D})$ 或 $\mathcal{D}^{\mathcal{C}}$：
> - 对象是 $\mathcal{C} \rightarrow \mathcal{D}$ 的函子
> - 任意两个对象 $F, G$ 间的态射是自然变换 $\theta : F \rightarrow G$
> - 恒等运算为自函子 $\operatorname{\mathrm{id}}\_{\mathcal{C}}$
> - 合成运算为自然变换的纵合成

函子范畴在 Haskell 中的表述如下：

```haskell
type instance (~>) = Nat
instance Category ((~>) :: i -> i -> *)
         => Category (Nat :: (k1 -> i) -> (k1 -> i) -> *) where
  id = Nat id
  Nat f . Nat g = Nat (f . g)
```

## 反范畴的函子范畴

根据前面的讨论，反范畴上的函子（即反函子）$F^{\mathrm{op}} : \mathcal{C}^{\mathrm{op}} \rightarrow \mathcal{D}^{\mathrm{op}}$ 与原函子 $F$ 等价，但是自然变换 $\theta^{\mathrm{op}}$ 取反。

即有 $\operatorname{\mathrm{Fct}}(\mathcal{C}, \mathcal{D}) \overset{\sim}{\rightarrow} \operatorname{\mathrm{Fct}}(\mathcal{C}^{\mathrm{op}}, \mathcal{D}^{\mathrm{op}})$，使得 $\theta \mapsto \theta^{op}$。

# 以自然变换为态射的 Cat 范畴

前面介绍的 Cat 范畴以小范畴为对象，以函子为态射。但是实际上可以换一种方式看 Cat 范畴，即仍然以小范畴为对象，但是以自然变换为态射。即：设范畴 $\mathcal{C}, \mathcal{D}$，函子 $F, G : \mathcal{C} \rightarrow \mathcal{D}$ 和自然变换 $\theta : F \rightarrow G$。令 $\theta$ 成为 $\mathcal{C} \rightarrow \mathcal{D}$ 的态射。

![Horizontal Cat](/img/in-post/post-algebra/horizontal-cat.svg){:height="500px" width="500px"}

下面证明这个新范畴 $\mathcal{N}$ 仍然满足范畴的定义。
- 对象 $\operatorname{\mathrm{Ob}}(\mathcal{N}) = \operatorname{\mathrm{Ob}}(\mathbf{Cat}) = \mathcal{C}, \mathcal{D}, \dots$
- 态射 $\operatorname{\mathrm{Hom}}(\mathcal{C}, \mathcal{D}) = \operatorname{\mathrm{Nat}}(F\_1, F\_2)\ (F\_1, F\_2 : \mathcal{C} \rightarrow \mathcal{D})$
- 单位态射 $\operatorname{\mathrm{idNat}}\_{\mathcal{C}} = \operatorname{\mathrm{id}}\_{\mathcal{C}} \rightarrow \operatorname{\mathrm{id}}\_{\mathcal{C}}\ (\operatorname{\mathrm{id}}\_{\mathcal{C}} : \mathcal{C} \rightarrow \mathcal{C})$
- 态射复合：自然变换的横向复合
  + 设 $\theta : \mathcal{C} \rightarrow \mathcal{D} = F\_1 \rightarrow F\_2,\ \psi : \mathcal{D} \rightarrow \mathcal{E} = G\_1 \rightarrow G\_2$
  + $\theta \circ \psi : \mathcal{C} \rightarrow \mathcal{E} = G\_1 F\_1 \rightarrow G\_2 F\_2$
  + 结合律即横向复合的结合律

因此这个范畴上态射的合成就是自然变换横合成的本质（对应函子范畴上态射的合成是纵合成的本质）。

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
