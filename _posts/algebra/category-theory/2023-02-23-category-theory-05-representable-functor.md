---
layout: "post"
title: "「范畴论」04 米田引理与可表函子"
subtitle: "Yoneda lemma and Representable functor"
author: "roife"
date: 2023-02-23

tags: ["代数@数学", "数学@Tags", "Haskell@编程语言", "范畴论@数学"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# Yoneda 嵌入

设局部小范畴 $\mathcal{C}$，定义**预层范畴**（presheaf category，即 $\mathcal{C}$ 到集合范畴的所有反变函子构成的函子范畴）：

$$
C^{\wedge} = \operatorname{\mathrm{Fun}}(\mathcal{C}^{\mathrm{op}}, \mathsf{Set})
$$

定义函子

$$
\begin{align*}
h_{\mathcal{C}} : \mathcal{C} & \rightarrow \mathcal{C}^{\wedge} \\
B & \mapsto \operatorname{\mathrm{Hom}}_{\mathcal{C}}(-, B)
\end{align*}
$$

$h\_{\mathcal{C}}$ 称为 **Yoneda 嵌入**（Yoneda Embedding），它将范畴嵌入到了函子范畴上。

定义求值函子

$$
\begin{align*}
\operatorname{\mathrm{ev}}^{\wedge} : \mathcal{C}^{\mathrm{op}} \times \mathcal{C}^{\wedge} & \rightarrow \mathsf{Set} \\
(A, F) & \mapsto F(A)
\end{align*}
$$

使用 yoneda lemma 可以证明 $h\_{\mathcal{C}}$ 是一个嵌入。

> 同时还可以定义对应的**反变 Yoneda 嵌入**（对偶范畴的 Yoneda 嵌入）：
>
> $$
> \mathcal{C}^{\vee} = \operatorname{\mathrm{Fun}}(\mathcal{C}^{\mathrm{op}}, \mathsf{Set}^{\mathrm{op}}) = \operatorname{\mathrm{Fun}}(\mathcal{C}, \mathsf{Set})^{\mathrm{op}}
> $$
>
> $$
> \begin{align*}
> h^{\mathcal{C}} : \mathcal{C} & \rightarrow \mathcal{C}^{\vee} \\
> A & \mapsto \operatorname{\mathrm{Hom}}_{\mathcal{C}}(A, -)
> \end{align*}
> $$
>
> 定义对应的求值函数：
>
> $$
> \begin{align*}
> \operatorname{\mathrm{ev}}^{\vee} : (\mathcal{C}^{\vee})^{\mathrm{op}} \times \mathcal{C} & \rightarrow \mathsf{Set} \\
> (F', A) & \mapsto F'(A)
> \end{align*}
> $$

# Yoenda 引理

> **Yoneda Lemma**：对于局部小范畴 $\mathcal{C}$，设 $T \in \operatorname{\mathrm{Ob}}(\mathcal{C})$ 与 $F \in \operatorname{\mathrm{Ob}}(\mathcal{C}^{\wedge})$（即 $F : \mathcal{C}^{\mathrm{op}} \rightarrow \mathsf{Set}$），有自然同构：
>
> $$
> \begin{align*}
> \Theta : \operatorname{\mathrm{Hom}}_{\mathcal{C}^{\wedge}}(h_{\mathcal{C}}(T), F) & \overset{\sim}{\rightarrow} F(T) \\
> \left [ \operatorname{\mathrm{Hom}}_{\mathcal{C}}(-, T) \overset{\phi}{\rightarrow} F \right] & \mapsto \phi_T(\operatorname{\mathrm{id}}_T)
> \end{align*}
> $$
>
> 它给出了函子同构 $\operatorname{\mathrm{Hom}}\_{\mathcal{C}^{\wedge}}(h\_{\mathcal{C}}(-), -) \overset{\sim}{\rightarrow} \operatorname{\mathrm{ev}}^{\wedge}$。

这个同构也可以记作 $\operatorname{\mathrm{Nat}}(\mathcal{C}(-, A), F) \cong FA$。

此外，同样有**反变 Yoneda 引理**（Co-Yoneda Lemma）：存在自然同构 $\operatorname{\mathrm{Hom}}\_{\mathcal{C}^{\vee}}(h^{\mathcal{C}}(S), F) \cong F()$，即 $\operatorname{\mathrm{Nat}}(\mathcal{C}(A, -), F) \cong FA$。它给出了函子同构 $\operatorname{\mathrm{Hom}}\_{\mathcal{C}}(-, h^{\mathcal{C}}(-)) \overset{\sim}{\rightarrow} \operatorname{\mathrm{ev}}^{\vee}$。

## 证明

为方便起见，下面证明 Yoneda 引理的反变形式：

$$
\begin{align*}
\Theta : \operatorname{\mathrm{Hom}}_{\mathcal{C}^{\vee}}(h^{\mathcal{C}}(S), F) & \overset{\sim}{\rightarrow} F(S) \\
\left [ \operatorname{\mathrm{Hom}}_{\mathcal{C}}(S, -) \overset{\phi}{\rightarrow} F \right] & \mapsto \phi_S(\operatorname{\mathrm{id}}_S)
\end{align*}
$$

- 设 $S \in \mathcal{C}$，对于每个 $x \in F(S) : \mathsf{Set}$，定义自然变换 $\Psi(x) : \operatorname{\mathrm{Hom}}\_{\mathcal{C}}(S, -) \Rightarrow F$，其在分量 $T \in \mathcal{C}$ 上的定义为：

  $$
  \begin{align*}
  \Psi(x)_T : \operatorname{\mathrm{Hom}}_{\mathcal{C}}(S, T) & \Rightarrow F(T) \\
  f & \mapsto \underbrace{(F(f))}_{\in \operatorname{\mathrm{Hom}}_{\mathsf{Set}(F(S), F(T))}}(x)
 \end{align*}
  $$

- 下面证明 $\Psi(x)$ 是一个自然变换。设 $A, B \in \mathcal{C}$，$f \in \operatorname{\mathrm{Hom}}\_{\mathcal{C}}(A, B)$。由于 $F$ 是函子，因此下图交换：
  ![Yoneda Lemma 1](/img/in-post/post-algebra/yoneda-lemma-1.svg){:height="700px" width="700px"}
- 因此 $\Psi(x)$ 是一个自然变换。下面证明 $\Psi = \Theta^{-1} : F(S) \rightarrow \operatorname{\mathrm{Nat}}(\operatorname{\mathrm{Hom}}\_{\mathcal{C}}(S, -), F)$
  + 证明 $\Theta \circ \Psi = \operatorname{\mathrm{id}}\_{F(S)}$，即 $(\Theta \circ \Psi)(x) = \Theta(\Psi(x)) = \Psi(x)\_A(\operatorname{\mathrm{id}}\_A) = F(\operatorname{\mathrm{id}}\_A)(x) = \operatorname{\mathrm{id}}\_{F(A)}(x)$
  + 证明 $\Psi \circ \Theta = \operatorname{\mathrm{id}}\_{\operatorname{\mathrm{Nat}}(\operatorname{\mathrm{Hom}}\_{\mathcal{C}}(S, -), F)}$
    - 即证明 $\Psi \circ \Theta(\phi) = \phi \Rightarrow \Psi(\phi\_A(\operatorname{\mathrm{id}}\_A)) = \phi$
    - $\iff \forall B \in \operatorname{\mathrm{Ob}}(\mathcal{C}),\ \forall f \in \operatorname{\mathrm{Hom}}\_{\mathcal{C}}(A, B),\ \Psi(\phi\_A(\operatorname{\mathrm{id}}\_A))\_B(f) = \phi\_B(f)$
    - $\iff (F(f))(\phi\_A(\operatorname{\mathrm{id}}\_A)) = \phi\_B(f)$
    - 令 $u\_A = \phi\_S(\operatorname{\mathrm{id}}\_A)$，由于 $\phi$ 是自然变换 ，因此下图交换：
      ![Yoneda Lemma 2](/img/in-post/post-algebra/yoneda-lemma-2.svg){:height="650px" width="650px"}
    - 从两个方向分别可以得到 $\phi\_B(f)$ 和 $(F(f))(u\_A)$，因此 $\phi\_B(f) = (F(f))(u\_A) = (F(f))(\phi\_A(\operatorname{\mathrm{id}}\_A))$

因此同构成立。

## 米田嵌入是全忠实的

可以利用 Yoneda lemma 证明 Yoneda 嵌入是一个嵌入（即一个全忠实函子）：
- 取 $F = h\_{\mathcal{C}}(X)$；
- 根据 Yoneda lemma，得 $\operatorname{\mathrm{Hom}}\_{\mathcal{C}^{\wedge}}(h\_{\mathcal{C}}(A), h\_{\mathcal{C}}(X)) \cong h\_{\mathcal{C}}(X)(A) = \operatorname{\mathrm{Hom}}\_{\mathcal{C}}(A, X)$ 是双射，因此是全忠实的；
- 同理可以证明 $h^{\mathcal{C}}$ 是全忠实的

由这条性质可以得出下面这个推论：

> 设局部小范畴 $\mathcal{C}$，$c, d \in \operatorname{\mathrm{Ob}}(\mathcal{C})$。$c \cong d \iff h\_{\mathcal{C}}(A) \cong h\_{\mathcal{C}}(X) \iff \operatorname{\mathrm{Hom}}(-, c) \cong \operatorname{\mathrm{Hom}}(-, d)$
>
> 即一个对象由它的态射所决定。

## Haskell 中的 Yoneda 引理

在 $\operatorname{\mathrm{Nat}}(\mathcal{C}(A, -), F)$ 中，Hom 函子实际上就是函数态射 `forall x. a -> x`，因此这个自然变换可以定义为 `Nat ((->) a) F`。

```haskell
{-# LANGUAGE ExistentialQuantification #-}

data Yoneda f a = Yoneda { runYoneda :: forall b. (a -> b) -> f b }
```

例如令 `f = Maybe` 且 `a = Bool`，则：

```haskell
mb1, mb2, mb3 :: Maybe Bool
mb1 = Nothing
mb2 = Just False
mb3 = Just True

ymb1, ymb2, ymb3 :: Yoneda Maybe Bool
ymb1 = Yoneda (\g -> Nothing)
ymb2 = Yoneda (\g -> Just $ g False)
ymb3 = Yoneda (\g -> Just $ g True)
```

并且可以定义出 `Yoneda` 和 `f a` 的同构关系：

```haskell
yphi :: Functor f => f a -> Yoneda f a
yphi x = Yoneda (\f -> fmap f x)

ypsi :: Yoneda f a -> f a
ypsi (Yoneda f) = f id
```

即三者是一一对应的：

$$
FA \cong \operatorname{\mathrm{Yoneda}}\ F\ A \cong \operatorname{\mathrm{Hask}}(A, -) \rightarrow FA
$$

借助 `yphi` 和 `ypsi`，可以为 `Yoneda` 实现 typeclasses：

```haskell
instance Functor f => Functor (Yoneda f) where
  fmap f y = yphi $ fmap f (ypsi y)

instance Applicative f => Applicative (Yoneda f) where
  pure a = yphi $ pure a
  y1 <*> y2 =
    let f = ypsi y1
        x = ypsi y2
    in yphi (f <*> x)

instance Monad m => Monad (Yoneda m) where
  return a = yphi $ return a
  ym >>= ayn =
    let m = ypsi ym
        n = \x -> ypsi (ayn x)
    in yphi (m >>= n)
```

此外，Yoneda 也可以定义为

```haskell
data Coyoneda f a = forall b. Coyoneda (b -> a) (f b)

instance Functor (Coyoneda f) where
  fmap f (Coyoneda g v) = Coyoneda (f . g) v

liftCoyoneda :: f a -> Coyoneda f a
liftCoyoneda f = Coyoneda id f

lowerCoyoneda :: Functor f => Coyoneda f a -> f a
lowerCoyoneda (Coyoneda g v) = fmap g v
```

Yoneda 引理带来的另一个启发就是，对于 `(a -> b) -> f b` 这样的函数可以直接用 `f a` 表示。

## Haskell 中的 Yoneda 嵌入

由 Yoneda 嵌入的证明可以得到同构关系：

```haskell
{-# LANGUAGE ExistentialQuantification #-}

data YonedaEmbed f a = YonedaEmbed { runYonedaEmbed :: forall x. (a -> x) -> (b -> x) }

yphi :: YonedaEmbed y => y -> (b -> a)
yphi y = (runYonedaEmbed y) id

ypsi :: YonedaEmbed y => (b -> a) -> y
ypsi btoa = YonedaEmbed $ \atox -> \b -> atox (btoa b)
```

这个同构可以看作是 CPS 编码，即 `(a -> x)` 是 `(b -> x)` 的 continuation。

# 可表函子

如果存在 $X \in \operatorname{\mathrm{Ob}}(\mathcal{C})$ 及同构 $\phi : h\_{\mathcal{C}}(X) \overset{\sim}{\rightarrow} F$（即 $\operatorname{\mathrm{Hom}}\_{\mathcal{C}}(-, X) \cong F$），则称 $F : \mathcal{C}^{\mathrm{op}} \rightarrow \mathsf{Set}$ 是**可表函子**（representable functor），并称 $(X, \phi)$ 是其**代表元**。

由 Yoneda 引理可知，$h\_{\mathcal{C}}(X) \rightarrow F$ 一定存在，且 $\phi$ 可以由 $u\_X = \phi\_X(\operatorname{\mathrm{id}}\_A)$ 表示；反过来则未必。

## Haskell 中的可表函子

$\operatorname{\mathrm{Hom}}\_{\mathcal{C}}(-, X)$ 可以定义为 `forall a. a -> x`。

```haskell
rphi :: forall x. (a -> x) -> F x
rpsi :: forall x. F x -> (a -> x)
```

例如列表函子 `[]` 是不可表的，因为逆变换 `[A] -> (B -> A)` 当 `[A]` 为空时不存在。

从 `rphi` 的定义中可以看出，在 Hask 范畴上，可表函子类似于将函数“存入”容器，而 `rpsi` 可以调用容器中的函数并取出值：

```haskell
class Representable f where
    type Rep f :: *
    tabulate :: (Rep f -> x) -> f x
    index    :: f x -> Rep f -> x
```

例如对于 `Stream`：

```haskell
data Stream x = Cons x (Stream x)

instance Representable Stream where
    type Rep Stream = Integer
    tabulate f = Cons (f 0) (tabulate (f . (+1)))
    index (Cons b bs) n = if n == 0 then b else index bs (n-1)
```

这蕴含着一种思想：函数和一些数据结构是同构的。
