---
layout: "post"
title: "「Haskell 学习」 06 More Typeclasses"
subtitle: "更多常用的 typeclasses"
author: "roife"
date: 2022-11-12

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags", "Functor@函数式编程"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# `Monoid`

`Monoid` 对应数学上的 monoid，即满足**结合性**并且**存在单位元**的代数结构 $(S, \oplus, 1)$。

通过 monoid 的写法可以看出，monoid 中实际上定义三个东西：集合、单位元以及满足结合律的运算。
- 集合可以在 `Monoid` 签名中看出
- 单位元通过 `mempty` 定义
- 运算通过 `mappend` 定义

```haskell
class Semigroup a => Monoid a where
  mempty :: a
  mappend :: a -> a -> a
```

对于同样的集合，也可以定义不同的 monoid。注意 `a` 本身不是 monoid，`Sum` 这个包含了 $(S, \oplus, 1)$ 的代数结构才是 monoid。

```haskell
-- 加法 monoid
newtype Sum a = Sum { getSum :: a } deriving (Eq, Ord, Read, Show, Bounded)

instance Num a => Monoid (Sum a) where
  mempty = Sum 0
  Sum x `mappend` Sum y = Sum (x + y)

-- 乘法 monoid
newtype Product a = Product { getProduct :: a } deriving (Eq, Ord, Read, Show, Bounded)

instance Num a => Monoid (Product a) where
  mempty = Product 1
  Product x `mappend` Product y = Product (x * y)
```

## Monoid law

- Left identity: ``mempty `mappend` x = x``
- Right identity: ``x `mappend` mempty = x``
- Associativity: ``(x `mappend` y) `mappend` z = x `mappend` (y `mappend` z)``

## 函数的自同态

函数的自同态（endomorphisms）即 `a -> a` 自己映射到自己。自同态 $(f :: a \rightarrow a, (.), \operatorname{\mathtt{id}})$ 也是 monoid，记作 `Endo`。

```haskell
newtype Endo a = Endo { appEndo :: a -> a }

instance Monoid (Endo a) where
  mempty = Endo id
  Endo f `mappend` Endo g = Endo (f . g)
```

自同态的对偶 $(f :: a \rightarrow a, (> > >), \operatorname{\mathtt{id}})$ 也是 monoid（`>>> :: (a -> b) -> (b -> c) -> (a -> c)`，即左结合的函数复合）。

```haskell
newtype FunApp a = FunApp { appFunApp :: a -> a }

instance Monoid (FunApp a) where
  mempty = FunApp id
  FunApp f `mappend` FunApp g = FunApp (g . f)
```

## 折叠

用 `foldl` 和 `foldr` 可以将 `(Monoid a, Foldable t) => t a` 折叠成一个值。

例如 `foldr (+) 0` 等价于 `Sum`。

## 对偶性

对于一个 monoid，它总是存在一个**对偶（dual）**，并且这个对偶也是单位半群。两个 monoid 的唯一区别就在于 `mappend` 函数的两个参数的顺序不同（本质上是因为满足结合律）。

```haskell
newtype Dual a = Dual { getDual :: a }

instance Monoid a => Monoid (Dual a) where
  mempty = Dual mempty
  Dual x `mappend` Dual y = Dual (y `mappend` x)
```

如果 monoid 的运算是可交换的（例如加法 monoid），那么其对偶就是自己。

## 其它 Monoid

- `()`

```haskell
instance Monoid () where
  mempty = ()
  mappend _ _ = ()
  mconcat _ = ()
```

- `Maybe a`

```haskell
instance Monoid a => Monoid (Maybe a) where
  mempty = Nothing
  Nothing `mappend` m = m
  m `mappend` Nothing = m
  Just m1 `mappend` Just m2 = Just (m1 `mappend` m2)
```

特别的是，即使 `a` 不是 monoid，也可以在 `Maybe a` 上面定义 monoid，但是运算和原来不一样。

```haskell
newtype First a = First { getFirst :: Maybe a }

instance Monoid (First a) where
  mempty = First Nothing
  r@(First (Just _)) `mappend` _ = r
  First Nothing `mappend` r = r

-- First 的对偶 Last
newtype Last a = Last { getLast :: Maybe a }

instance Monoid (Last a) where
  mempty = Last Nothing
  _ `mappend` r@(Last (Just _)) = r
  r `mappend` Last Nothing = r
```

对于 `First`，$m\_1 \oplus m\_2 \oplus m\_3 \dots$ 会返回第一个 `Just`，如果全为 `Nothing` 则返回 `Nothing`；`Last` 恰好相反，总是返回最后一个 `Just`。

- 函数 `a -> b`：如果 `b` 是一个 monoid，则 `a -> b` 上也可以定义 monoid。

```haskell
instance Monoid b => Monoid (a -> b) where
  mempty _ = mempty
  mappend f g x = f x `mappend` g x
```

## `Semigroup`

在 monoid 的条件里去掉单位元（只剩下结合律），那么可以构成半群 `Semigroup`。

开启 `DefaultSignatures` 扩展后，可以在 typeclasses 中给函数写默认的签名和定义。

```haskell
class Semigroup a where
  (<>) :: a -> a -> a

  default (<>) :: Monoid a => a -> a -> a
  (<>) = mappend

  sconcat :: NonEmpty a -> a
  sconcat (a :| as) = go a as where
    go b (c:cs) = b <> go c cs
    go b []     = b

  stimes :: Integral b => b -> a -> a
  stimes n a
      | n <= 0    = mempty
      | otherwise = go n a mempty
      where
      go n' x y
          | even n'    = go (n' `quot` 2) (x <> x) y
          | n' == 1    = x <> y
          | otherwise  = go ((n' - 1) `quot` 2) (x <> x) (x <> y)
```

- `<>` 是半群上的结合运算
- `sconcat` 等价于 `foldr1 (<>)`，`stimes` 等价于 `sconcat . replicate n`；这里之所以提供这两个函数是因为这两个函数常常会被用到，而且对于特殊的容器（例如列表）利用结合律可以实现特例化的加速版本

类似的，Cable 上还有 `Group` 包，可以定义 `Group`、`Cyclic` 和 `Abelian` 等。

# `Foldable`

实现了 `Foldable` 的类型拥有“遍历容器”的能力。

```haskell
class Foldable (t :: * -> *) where
  fold :: Monoid m => t m -> m
  fold = foldMap id

  foldMap :: Monoid m => (a -> m) -> t a -> m
  foldMap f = foldr (mappend . f) mempty

  foldr :: (a -> b -> b) -> b -> t a -> b
  foldr f z t = appEndo (foldMap (Endo . f) t) z

  foldl :: (b -> a -> b) -> b -> t a -> b
  foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z
  {-# MINIMAL foldMap | foldr #-}
```

**`foldMap` 会将容器内的值映射到一个 `Monoid`，然后通过二元运算结合起来。**对应的 `fold` 则是不映射直接折叠。

需要区分的是，`Foldable` 是一个比“容器的结构”（catamorphism）更弱一些的概念。实现了 `Foldable` 的类型提供了“以某种顺序遍历容器”的能力，本质上等价于拥有 `toList` 的能力。但是对于更复杂的结构操作，仅使用 `Foldable` 是无法做到的，例如无法使用 `Foldable` 相关的函数来计算树的高度。

## FTP

FPT 是的是 Foldable-Traversable in Prelude proposal。在 GHC 7.10 之前，`length` 之类的函数的定义是 `length :: [a] -> Int`。

FTP 将一些基于列表的函数进一步抽象到所有实现了 `Foldable` 和 `Traversable` 类型类的容器。老的函数被放在 `GHC.OldList` 中。

## 元组和 `Either`

值得注意的是 `Foldable` 在元组和 `Either` 类型上的实现。

```haskell
instance Foldable ((,) a) where
  foldMap :: forall m a. Monoid m => (a -> m) -> (a, a) -> m
  foldMap f (_, y) = f y

  foldr f z (_, y) = f y z
  length _  = 1
  null _ = False
```

这是因为二元元组的含义并不是“两个元素”，而是“一个元素伴随着一个 context”。因此 `foldMap` 只会对第二个元素进行处理。

在 `Either` 也是一样，只会在第二个参数上应用函数。

## Duality Theorem

- 第一对偶定理：对于 monoid $(M, \oplus, u)$，$\operatorname{\mathtt{foldr}}\ \oplus\ u\ xs = \operatorname{\mathtt{foldl}}\ \oplus\ u\ xs$
- 第二对偶定理：对于两个运算 $\oplus, \otimes$，若存在 $e$ 满足 $x \oplus (y \otimes z) = (x \oplus y) \otimes z$，则 $\operatorname{\mathtt{foldr}}\ \oplus\ u\ xs = \operatorname{\mathtt{foldl}}\ \otimes\ u\ xs$
- 第三对偶定律：对于列表 `xs`，都有 $\operatorname{\mathtt{foldr}}\ f\ u\ xs = \operatorname{\mathtt{foldl}}\ (\operatorname{\mathtt{flip}} f)\ e\ (\operatorname{\mathtt{reverse}}\ xs)$，其中 $u, e$ 分别为 $f, \operatorname{\mathtt{flip}}\ f$ 的单位元

（上面三条定理中的 `xs` 都是有限，因为对于无穷列表 `foldl` 无法停机）

通过这三条对偶定理，可以把 `foldr` 转换为 `foldl`，而后者是尾递归定义的，计算效率更高（不考虑惰性求值带来的影响）。

# `Functor`

```haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b

infixl 4 <$>
(<$>) :: Functor f => (a -> b) -> f a -> f b
(<$>) = fmap
```

`Functor` 有两种直观的理解：
- `f` 是一个容器；`fmap` 可以对容器内的值进行映射，且不会改变容器的结构
- `f` 是一种“可计算的上下文”（computational context）；`fmap` 可以对值进行映射，且不会改变上下文

`fmap` 的类型也可以看成一个 lift `(a -> b) -> (f a -> f b)`，理解为“给定两个类型上的一个映射，返回参数化类型上对应的映射”。

```haskell
instance Functor Maybe where
  fmap f Nothing = Nothing
  fmap f (Just x) = Just (f x)

-- 对于一种特殊的树类型
data Tree a = Leaf a | Branch (Tree (a, a)) deriving Show

instance Functor Tree where
  fmap f (Leaf a) = Leaf (f a)
  fmap f (Branch t) = Branch $ (\(a, b) -> (f a, f b)) <$> t
```

可以证明，一个类型如果实现为 functor，那么其 `fmap` 的实现是唯一的。

## 函数 functor

`((->) r)`（或者看成 `r -> ...`）也是一个函子，定义如下：

```haskell
instance Functor ((->) r) where
    fmap = (.)
```

`(r -> a)` 可以看做 `a` 类型对应的值的一个集合，其中 `r` 为值的索引（indeces）。而 `(.)` 表示对函数的返回结果进行映射，即对集合中的每个元素进行映射。

## 常见 functors 的含义

- `[]`：不确定的选择（nondeterministic choice），某个值的多种可能的结果
- `Maybe`：可能失败的值（possible failure）
- `Either e`：和 `Maybe` 类似，代表一种可能失败的情况，但是它在失败时可以携带额外的错误信息（类型为 `e`）
- `(,) e`：携带额外的注解信息（annotations，类型为 `e`）的容器
- `(->) e`：一个 reader，其中 `e` 是被读取的值

## 函子定律

- `fmap id = id`（左侧的类型为 `a -> a`，右侧的类型为 `f a -> f a`）
- `fmap (f . g) = (fmap f) . (fmap g)` 利用这一条可以优化代码

要成为 functor，不仅要定义出 `fmap`，还要满足上面的定律。例如 `Set` 定义出的 `fmap` 无法满足第一条定律，因此不是 functor。

如果不考虑 $\bot$，那么第二条定律可以从第一条中推导出来：

```haskell
-- Free Theorem
        f .      g =      p .      q
=> fmap f . fmap g = fmap p . fmap q

-- Choose p = id, q = f . g
fmap f . fmap g
= fmap id . fmap (f . g)
= id . fmap (f . g)
= fmap (f . g)
```

## `<$`，`$>` 与 `void`

```haskell
(<$) :: Functor f => a -> f b -> f a
(<$) = fmap . const
```

`<$` 等价于 `\a (f b) -> fmap (const a) (f b)`，即将容器 `f b` 中的值直接替换为 `a`。

类似的：

```haskell
($>) :: Functor f => f a -> b -> f a
($>) = flip (<$)

void :: Functor f => f a -> f ()
void = (<$) ()
```

# `Applicative`

`Applicative` 一定是 `Functor`（全名为 applicative functor）。

```haskell
infixl 4 <*>

class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
```

`pure` 可以把一个东西包到容器里，而 `(<*>)` 则可以将容器中的运算应用到容器中的值上。此处的“容器”指广义的容器，包括函数等。

可以用这两个定义 `fmap f fa = pure f <*> fa`。

`(<*>) :: f (a -> b) -> f a -> f b` 的签名和 `($) :: (a -> b) -> a -> b` 比较像。

## `<$>`，`<*>` 与 `liftA`

借助 `<*>` 与 `pure`，可以将一个外部的**多元**运算应用到容器中的值上（使用柯里化）：

```haskell
> (+) <$> Just 5 <*> Just 4
Just 9

> pure (+) <*> Just 5 <*> Just 4
Just 9
```

可以看出 `f <$> a1 <*> a2 <*> ... <*> an` 等价于 `pure f <*> a1 <*> a2 <*> ... <*> an`。

`liftA` 就是这么定义的，可以将运算“提升”到容器中。其中 `liftA` 是最简单的一个 `lift`，和 `<$>` 等价

```haskell
liftA :: Applicative f => (a -> b) -> f a -> f b
liftA f a = pure f <*> a
-- liftA = <$>

liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f a b = f <$> a <*> b

> liftA2 (+) (Just 5) (Just 4)
Just 9
```

## `<*` 与 `*>`

- `<*` 计算两侧的表达式，并只返回前一次的结果
- `*>` 计算两侧的表达式，并只返回后一次的结果

```haskell
infixl 4 <*, *>

(*>) :: f a -> f b -> f b
u *> v = const id <$> u <*> v
-- *> = liftA (const id)

(<*) :: f a -> f b -> f a
u <* v = const <$> u <*> v
-- <* = liftA const
```

## `List` applicative 与函数 applicative

列表也能实现 Applicative，并且类似于 list comprehension，这是因为列表象征着“有多种可能性”，因此需要对所有的值都进行计算：

```haskell
instance Applicative [] where
  pure x = [x]
  fs <*> xs = [f x | f <- fs, x <- xs]
```

```haskell
-- [x+y| x <- [1,2], y <- [3,4]]
> (+) <$> [1,2] <*> [3,4]
[4, 5, 5, 6]
```

但是对于同一种类型可以有多种 applicative 的定义。如果只是将列表看作一个容器，那么定义如下：

```haskell
newtype ZipList a = ZipList { getZipList :: [a] }

instance Applicative ZipList where
  pure :: a -> ZipList a
  pure = ZipList . repeat

  (<*>) :: ZipList (a -> b) -> ZipList a -> ZipList b
  (ZipList gs) <*> (ZipList xs) = ZipList (zipWith ($) gs xs)
```

`(->) r` 也是一个 applicative：

```haskell
instance Applicative ((->) r) where
  -- pure :: a -> (r -> a)
  pure x _ = x

  -- (<*>) :: (r -> a -> b) -> (r -> a) -> r -> b
  (<*>) f g x = f x (g x)
```

## Applicative 定律

- Identity: `pure id <*> v = v`
- Composition: `pure (.) <*> u <*> v <*> w = u <*> (v <*> w)`
- Homomorphism: `pure f <*> pure x = pure (f x)`
- Interchange: `u <*> pure y = pure ($ y) <*> u`

## Applicative 的本质（与 Functor 的区别）

`Applicative` 本质上是一个 `MultiFunctor`，把一般的函数提升到了参数化类型 `f` 上，这也是  `liftA` 的由来。

```haskell
import Control.Applicative
class MultiFunctor f where
  -- 等价于 pure
  fmap0 :: a -> f a

  -- 等价于 fmap
  fmap1 :: (a -> b) -> f a -> f b

  -- 用 pure 和 <*> 定义 fmap2
  fmap2 :: (a -> b -> c) -> f a -> f b -> f c
  fmap2 h x y = pure h <*> x <*> y

  -- 有了前面的 3 个函数就可以定义任意多元的 fmap
  fmap3 :: (a -> b -> c -> d) -> f a -> f b -> f c -> f d
  fmap3 h x y z = fmap2 ($) (fmap2 h x y) z

  fmap4 :: (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
  fmap4 h w x y z = fmap2 ($) (fmap3 h w x y) z
```

与 functor 相比，applicative 能够将多次应用的函数 `a -> b -> c` 应用在值 `f a`、`f b` 上。在 functor 中，如果用 `(a -> b -> c) <$> (f a)`，则会得到一个 `f (b -> c)`，无法再应用 `f b`；而借助 `<*> :: f (a -> b) -> f a -> f b`，则可以将这个操作继续下去。

## Applicative 的另一种定义

Applicative 还可以定义成下面这种形式：

```haskell
class Functor f => Monoidal f where
  unit :: f ()
  (**) :: f a -> f b -> f (a, b)
```

下面的代码表明 monoidal 和 applicative 可以互定义，因此二者等价：

```
-- Monoidal 定义 Applicative
pure' :: Monoidal f => a -> f a
pure' x = fmap (const x) unit

ap' :: Monoidal f => f (a -> b) -> f a -> f b
ap' f x = fmap (\(g, y) -> g y) (f ** x)


-- Applicative 定义 Monoidal
unit' :: Applicative f => f ()
unit' = pure ()

(**') :: f a -> f b -> f (a, b)
(**') fa fb = pure (,) <*> fa <*> fb
```

Monoidal functor 的两个操作分别对应 monoid 的 `mempty` 和 `mappend`，因此也满足 monoid 定律：
- Left identity: `unit ** v = v`
- Right identity: `u ** unit = u`
- Associativity: `u ** (v ** w) = (u ** v) ** w`

这三条定律与 applicative 定律等价。并且在范畴论中，还要求 monoidal functor 满足 naturality `fmap (g *** h) (u ** v) = fmap g u ** fmap h v`。

# `Alternative`

`Alternative` 依赖于 `Applicative`，表达了“允许计算失败，可以选择其它方案”的含义。

```haskell
infixl 3 <|>

class Applicative f => Alternative f where
  empty :: f a
  (<|>) :: f a -> f a -> f a
```

例如，`Maybe` 是一个 `Alternative`：

```haskell
instance Alternative Maybe where
  empty = Nothing
  Nothing <|> p = p
  Just x <|> _ = Just x

> Nothing <|> Nothing <|> Just 1 <|> Just 2
Just 1
```

通常来说，`Alternative` 是一个 `Monoid`，因此满足 monoid laws：
- Left identity: `empty <|> u  =  u`
- Right identity: `u <|> empty  =  u`
- Associativity: `u <|> (v <|> w)  =  (u <|> v) <|> w`

## `List` alternative

比较有趣的是 `List` alternative。列表的含义是“多种可能性”，因此列表 alternative 是将所有可能性综合，即 `(++)`。

```haskell
instance Alternative [] where
  empty = []
  (<|>) = (++)
```

## `some` 与 `many`

这两个函数在写 parser 的时候很常用：

```haskell
some :: f a -> f [a]
some v = some_v
  where
    many_v = some_v <|> pure []
    some_v = (:) <$> v <*> many_v

many :: f a -> f [a]
many v = many_v
  where
    many_v = some_v <|> pure []
    some_v = (:) <$> v <*> many_v
```

`some` 表示返回“一个或多个”，`many` 表示返回“零个或多个”。

- 对于 `some_v` 来说，匹配一个，得到的结果放到列表头部 `(:)`，然后用 `many_v` 匹配“零个或多个”。
- 对于 `many_v` 来说，如果能匹配（`some_v` 会匹配一个，然后递归调用 `many_v` 匹配剩下的，因此能匹配“一个或多个”），那么匹配，否则返回 `pure []`

从这里也可以看出列表表示“多种可能性”。

## `optional` 函数

```haskell
optional :: Alternative f => f a -> f (Maybe a)
optional v = Just <$> v <|> pure Nothing

> optional [1, 2, 3]
[Just 1, Just 2, Just 3, Nothing]
```

`optional` 函数表示对容器内的所有值尝试进行计算，并对失败的结果返回 `Nothing`。在写 parser 时非常好用。

# `Traversable`

`Traversable` 本质上是一个 `Foldable` 的 `Functor`，但是在 `fmap` 的同时允许执行一些 effects（所以结果类型是 `f (t b)`）。

```haskell
class (Functor t, Foldable t) => Traversable t where
  traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
  traverse f = sequenceA . fmap f

  sequenceA :: Applicative f => t (f a) -> f (t a)
  sequenceA = traverse id
  {-# MINIMAL traverse | sequenceA #-}
```

并非对于所有的 functor 和 foldable 都可以实现 traversable，`Traversable` 类型其实包含了“交换性”。

## 实现 `Traversable`

- 列表实现 `traversable`：

```haskell
traverse _ [] = pure []
traverse f (x:xs) = (:) <$> f x <*> traverse f xs

sequenceA [] = pure []
sequenceA (x:xs) = (:) <$> x <*> sequenceA xs
```

- 树实现 `traverse`：

```haskell
data Tree a = Leaf a | Node (Tree a) a (Tree a) deriving (Show, Foldable, Functor)

instance Traversable Tree where
  -- traverse :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
  traverse f (Leaf a) = Leaf <$> f a
  traverse f (Node l a r) = Node <$> traverse f l <*> f a <*> traverse f r

  -- sequenceA :: Applicative f => Tree (f a) -> f (Tree a)
  sequenceA (Leaf a) = Leaf <$> a
  sequenceA (Node l a r) = Node <$> sequenceA l <*> a <*> sequenceA r
```

可以发现对于 `Applicative`，`sequenceA` 通常定义为 `cons <$> sequenceA a1 <*> sequenceA a2 <*> ... <*> sequenceA an`，即先翻转每个元素，然后将内部元素拿出来 construct。

## 定义 `Functor` 和 `Foldable`

`Traversable` 在实现时并没有用到 `fmap`，实际上 `Traversable` 本身是特殊化的 `Functor`，下面利用 `traverse` 来定义 `fmap`。

在定义过程中需要用到 `Identity` 和 `Constant` 两个 functor。

```haskell
newtype Identity a = Identity { runIdentity :: a }

instance Functor (Identity a) where
  fmap f (Identity a) = Identity (f a)

instance Foldable (Identity a) where
  foldMap f (Identity a) = f a

instance Applicative (Identity a) where
  pure = Identity
  Identity f <*> Identity a = Identity (f a)

instance Traversable (Identity a) where
  traverse f (Identity x) = f <$> Identity a
```

```haskell
newtype Constant a b = Constant { getConstant :: a }

instance Functor (Constant a b) where
  -- fmap :: (b -> b1) -> Constant a b -> Constant a b1
  fmap f (Constant x) = Constant a

instance Foldable (Constant a b) where
  -- foldMap :: Monoid a => (a -> m) -> Constant a1 a -> m
  foldMap f (Constant a) = mempty

instance (Monoid a) => Applicative (Constant a) where
  pure _ = Constant mempty
  Constant x <*> Constant y = Constant (x `mappend` y)

instance Traversable (Constant a) where
  -- traverse :: Applicative f => (a1 -> f b) -> Constant a a1 -> f (Constant a b)
  traverse f (Constant x) = pure (Constant x)
```

下面定义 `fmap'` 和 `foldMap'`：

```haskell
fmap' :: Traversable t => (a -> b) -> t a -> t b
fmap' f x = runIdentity $ traverse (Identity . f) x  -- 相当于用 Identity Functor 实现映射后不变
```

```haskell
foldMap' :: (Traversable t, Monoid m) => (a -> m) -> t a -> m
foldMap' f x = getConstant $ traverse (Constant . f) x
```

区别在于二者在 `(<*>)` 的表现不一样。

## `Traversable` 定律

- `traverse Identity = Identity`：即 `traverse` 本身不带 effects
- `traverse (Compose . fmap g . f) = Compose . fmap (traverse g) . traverse f`：定义了 `traverse` 的组合方式

# 其它常用 typeclasses

## `Ord`

``` haskell
class (Eq a) => Ord a where
  compare :: a -> a -> Ordering
  (<), (<=), (>), (>=) :: a -> a -> Bool
  max, min :: a -> a -> a

  compare x y =
    if x == y then EQ
    else if x <= y then LT
    else GT

  x < y = case compare x y of { LT -> True; _ -> False }
  x <= y = case compare x y of { GT -> False; _ -> True }
  x > y = case compare x y of { GT -> True; _ -> False }
  x >= y = case compare x y of { LT -> False; _ -> True }
  max x y = if x <= y then y else x
  min x y = if x <= y then x else y
  {-# MINIMAL compare | (<=) #-}
```

## `Bounded`

```haskell
class Bounded a where
  minBound, maxBounded :: a
```

## `Enum`

```haskell
class Enum a where
  toEnum :: Int -> a
  fromEnum :: a -> Int
  succ, pred :: a -> a
  enumFrom :: a -> [a]                 -- [n..]
  enumFromThen :: a -> a -> [a]        -- [n,n'..]
  enumFromTo :: a -> a -> [a]          -- [n..m]
  enumFromThenTo :: a -> a -> a -> [a] -- [n,n'..m]
  {-# MINIMAL toEnum, fromEnum #-}
```

如果所有的 constructor 都没有参数，那么可以直接使用 `deriving` 来导出 `Enum`。

## `Ix`

`Ix` 可以将类型中连续的值映射到整数：

```haskell
class (Ord a) => Ix a where
  range :: (a,a) -> [a]
  index :: (a,a) -> a -> Int
  GHC.Arr.unsafeIndex :: (a,a) -> a -> Int
  inRange :: (a,a) -> a -> Bool
  rangeSize :: (a,a) -> Int
  GHC.Arr.unsafeRangeSize :: (a,a) -> Int
  {-# MINIMAL range, (index | unsafeIndex), inRange #-}
```

`range` 传入一个区间的两端，会返回整个区间：

```haskell
-- data Weekday = Mon | Tue | Wed | Thu | Fri | Sat |Sun deriving (Eq,Ord,Ix,Show)

> range (Mon, Sun)
[Mon,Tue,Wed,Thu,Fri,Sat,Sun]
```

## `Show`

```haskell
class Show a where
  showsPrec :: Int -> a -> ShowS
  show :: a -> String
  showList :: [a] -> ShowS
  {-# MINIMAL showsPrec | show #-}
```

### `ShowS`

这里有一个 `ShowS :: String -> String`，它能起到 `StringBuilder` 的作用，快速连接多个字符串。

在普通情况下，依次连接数个字符串 $s\_1, s\_2, \dots, s\_n$ 的复杂度为 $O(n^2)$（因为需要将前一个字符串的字符一个个放到第二个字符串的开头）。但是如果从后往前连接（按照 $s\_n, s\_{n-1}, \dots, s\_1$），则复杂度为 $O(n)$。因此可以将所有字符串存到一个闭包中，当需要转换为字符串时，再从后往前转换成字符串：

在 Haskell 中可以用 `shows` 将可显示类型转换为 `ShowS`，也可以用 `showChar` 和 `showString` 将字符和字符串转换为 `ShowS`（区别在于后者得到的字符串没有带引号）：

```haskell
- (shows 5 . showString " Apples") "."
"5 Apples."
```

### `showPrec`

`showPrec :: Int -> a -> ShowS` 一般用于打印语法树。

其中传入的第一个参数为外层的优先级加一，如果里面的运算低于这个优先级，那么应该打印括号。

```haskell
newtype Identity a = Identity { runIdentity :: a }

-- 11 表示如果内层还有包装，则必须加括号
instance (Show a) => Show (Identity a) where
  showsPrec d (Identity x) =
    showParen (d > 10) $ showString "Identity " . showsPrec 11 x
```

## `Read`

```haskell
class Read a where
  readsPrec :: Int -> ReadS a
  readList :: ReadS [a]
  GHC.Read.readPrec :: Text.ParserCombinators.ReadPrec.ReadPrec a
  GHC.Read.readListPrec :: Text.ParserCombinators.ReadPrec.ReadPrec [a]
  {-# MINIMAL readsPrec | readPrec #-}
```

这里 `ReadS a :: String -> [(a, String)]`。得到的列表为所有可能的解析结果，如果列表为空则代表解析失败。

`readsPrec` 中传入的整数表示外层函数的优先级加一，如果这个整数大于里面的优先级，则需要多读入一个括号。

```haskell
newtype Identity a = Identity { runIdentity :: a }

instance (Read a) => Read (Identity a) where
  readsPrec d = readParen (d > 10) $ \r ->
    [(Identity x,t) | ("Identity",s) <- lex r, (x,t) <- readsPrec 11 s]
```

## `IsString`

Haskell 中有多重字符串类型，如 `ByteString`（`[Word8]`）、`Text`（编码后的标准格式）等。

```haskell
class IsString a where
  fromString :: String -> a
```

开启 `OverloadedStrings` 扩展后，Haskell 能够自动转换不同类型的字符串：

```haskell
> Data.Text.map toUpper $ "abc"
"ABC"
```

## `Num`

```haskell
class Num a where
  (+), (-), (*) :: a -> a -> a
  negate :: a -> a
  abs :: a -> a
  signum :: a -> a
  fromInteger :: Integer -> a
  x - y = x + negate y
  negate x = 0 - x
  {-# MINIMAL (+), (*), abs, signum, fromInteger, (negate | (-)) #-}
```

值得注意的是，`Num` 不依赖 `Show` 或 `Eq`，例如可以定义这样一个特殊的类型：

```haskell
instance Num b => Num (a -> b) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  abs = liftA abs
  signum = liftA abs
  negate = fmap negate
  fromInteger = pure . fromInteger
```

那么 `(f + g) x = f x + g x`（很符合直觉）。

## `Bifunctor`

前面拥有两个类型参数的类型通常都只在第二个参数上进行操作（例如 `Either`），如果需要在两个参数上都进行操作，可以用 `Bifunctor`。

```haskell
class Bifunctor p where
  bimap :: (a -> b) -> (c -> d) -> p a c -> p b d
  bimap f g = first f . second g

  first :: (a -> b) -> p a c -> p b c
  first f = bimap f id

  second :: (b -> c) -> p a b -> p a c
  second = bimap id
  {-# MINIMAL bimap | first, second #-}
```

对于 `(,)` 和 `Either` 可以用 `Bifunctor` 对两个参数都进行映射：

```haskell
> bimap (+1) not (10, False)
(11,True)
```

类似还有 `Biapplicative`、`Bifoldable` 以及 `Bitraversable` 等。

# Typeclasses 层次

![Hierarchy](/img/in-post/post-haskell/typeclasses-hierarchy.svg)
