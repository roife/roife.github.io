---
layout: "post"
title: "「Haskell 学习」 07 Monad"
subtitle: "Monad，以及 AMP"
author: "roife"
date: 2022-11-14

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags", "Functor@函数式编程", "Monad@函数式编程"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# Monad 的定义

```haskell
class Applicative m => Monad m where
    return :: a -> m a
    (>>=) :: m a -> (a -> m b) -> m b

    (>>) :: m a -> m b -> m b
    m >> k = m >>= \_ -> k
    {-# MINIMAL (>>=) #-}
```

其中最重要的是 `>>=`，它能够将运算连接起来，并能够**使用前面计算的结果**。

`>>` 本质上是 `*>`，会进行前面的计算（可能存在副作用），但是会忽略返回值。

## `>>=` 与 do notation

`>>=` 的一个重要作用是连接运算，并且对 monad 进行拆包，以获得本次运算的结果，例如使用 Maybe monad 时（由于 `>>=` 的优先级为 1，因此无需添加括号）：

```haskell
\a -> Just a >>= \b -> Just (b + 5) >>= \c -> Just (c * 3)
```

这个表达式可以写成一种更直观的形式：

```haskell
\a ->
  Just a >>= \b ->
  Just (b + 5) >>= \c ->
  Just (c * 3)
```

其中，`b` 为 `Just a` 计算后的内部结果；`c` 为 `Just (b + 5)` 内部计算的结果。如果要再接一个计算，则可以得到 `c * 3` 的计算结果。运算中虽然接了多次 `>>=`，但是中间任何一段 `m >>= f` 的类型都是 `a -> Maybe a`。

本质上，这是一个**闭包**，其中内层闭包可以访问外层闭包的参数。

```haskell
\a -> Just a >>= (
  \b -> Just (b + 5) >>= (
    \c -> Just (c * 3)
  )
)
```

上面的写法可以写成 do notation 的形式，即用 `do` 和 `<-` 来化简：

```haskell
\a -> do
  b <- Just a
  c <- Just b
  return $ c * 3
```

如果写成一行，应该加上 `{}` 和 `;`：

```haskell
\a -> do { b <- Just a; c <- Just b; return $ c * 3 }
```

这种写法和命令式的写法非常像，这是利用了闭包的嵌套来保证求值顺序（用到了 `x` 就必须先对 `x` 进行求值）。

在看新的 monad 时，最重要的是看 `>>=` 的实现，因为 `<-` 的含义由 `>>=` 决定。对于 `m >>= f`，实现里 `f x` 中的 `x` 即为 `<-` 读出来的值，其他部分则为副作用。

## Monad laws

- Left identity: `return x >>= f = f x`
- Right identity: `m >>= return = m`
- Associativity: `(m >>= f ) >>= g = m >>= (λx → f x >>= g)`

## 常用函数

- `filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]`
  + 将合法的值收集到 `ys :: [a]` 里，然后 `return ys`
  + 可以定义 `powerSet xs = filterM (\x -> [False, True]) xs`
  + `mfilter :: (MonadPlus m) => (a -> Bool) -> m a -> m a` 取出值并判断
    + `mfilter p ma = do { a <- ma; if p a then return a else mzero }`
- `foldM :: (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b`
  + 相当于 `foldl`
  + 带下划线的会忽略结果：`foldM_ :: (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m ()`
- `(<=<) :: Monad m => (b -> m c) -> (a -> m b) -> a -> m c`
  + 相当于 `(.)`，优先级为 1
- `(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)`
  + 相当于 `(>>>)`，优先级为 1

不难发现，`|>` 对应 `>>=`，`(.)` 对应 `(<=<)`，`(>>>)` 对应 `(>=>)`。

### 模拟控制流

模拟控制流

`Control.Monad` 中提供了一些可以模拟控制流的 monad：

| 函数 | 作用 |
| - | - |
| `forever :: Applicative m => m a -> m b` | 永远执行给定参数 |
| `when :: Applicative m => Bool -> m () -> m ()` | 符合条件时，执行参数 |
| `unless :: Applicative m => Bool -> m ()-> m ()` | 不符合条件时，执行参数 |

```haskell
forever :: Applicative f => f a -> f b
forever a = let a' = a *> a' in a'

when :: Applicative f => Bool -> f () -> f ()
when p s =ifpthenselsepure()

unless :: Applicative f => Bool -> f () -> f ()
unless p s = if p then pure () else s
```

`forever` 函数会一直运行给定的 monad 值产生的行为，可以用在网络服务监听网络端口中。虽然 `forever` 不会返回任何的结果，但是其返回类型为 `m b`，**说明它可以当作任何类型使用**。

`when` 和 `unless` 用作 debug 时很方便，例如 `when debug (print "Debugging")`。

此外，还有下面几个函数：
- `replicateM :: Monad m => Int -> m a -> m [a]`：重复执行并记录结果
  + `replicateM_` 类似，但是忽略结果
- `sequence :: Monad m => [m a] -> m [a]`：将多个 Monad 值的列表串连起来并记录结果
  + `sequence_` 类似，但是忽略结果

# Monad 相关 typeclasses

## `MonadPlus`

`MonadPlus` 本质上是 `Alternative`，因为历史原因，两个没有合并。但是由于 `MonadPlus` 是基于 `Monad` 的，因此它可以和 `Monad` 进行操作，可以得到更强的性质。

```haskell
class Monad m => MonadPlus m where
  mzero :: m a
  mplus :: m a -> m a -> m a
```

一般来说，`MonadPlus` 也是一个 `Monoid`，因此可以用 `MonadPlus` 来实现 `Monoid`：

```haskell
instance MonadPlus m => Monoid (m a) where
  mempty = mzero
  mappend = mplus
```

因此 `MonadPlus` 通常也满足 `Monoid` laws。

还有一些 laws，没有规定 `MonadPlus` 需要满足，因此只是对于有些结构成立：
- Left Zero: `mzero >>= k = mzero`
- Right Zero: `ma >>= (\a -> mzero) = mzero`
- Left Distribution: `mplus a b >>= k = mplus (a >>= k) (b >>= k)`

对于 List monad 来说，只有有限列表才满足上面两条规则。

## `MonadFail`

`MonadFail` 和 `MonadPlus` 都表达了“计算失败”的概念，但是 `MonadPlus` 中的计算失败是“可恢复的”（使用 `mplus`）；而 `MonadFail` 的失败是“不可恢复的”，并且可以返回错误信息。

`Reader`、`State` 等 monad 没有实现 `MonadFail`。

```haskell
class Monad m => MonadFail m where
  fail :: String -> m a
```

`fail` 满足 `fail s >>= m = fail s`。

# 常见 monad

## `Identity` monad

Identity monad 是最简单的 monad，仅仅定义了一个容器，并且不伴随任何行为。

```haskell
newtype Identity a = Identity { runIdentity :: a } deriving (Functor)

instance Applicative Identity where
    pure = Identity
    (<*>) (Identity f) (Identity a) = Identity (f a)

instance Monad Identity where
    return = Identity
    Identity m >>= k = k m
```

## `Maybe` monad

Maybe monad 包含两种状态：正常状态（`Just`）和计算失败的状态（`Nothing`）。

```haskell
data Maybe a = Just a | Nothing deriving (Functor)

instance Applicative Maybe where
  pure = Just
  Just f <*> Just a = Just (f a)
  _ <*> _ = Nothing

instance Monad Maybe where
  return = Just
  (Just a) >>= f = f a
  Nothing >>= _ = Nothing
  fail _ = Nothing
```

从 `Nothing >>= _` 的定义中可以看出，中途计算一旦失败，那么后续运算就会被全部忽略。

## `List` monad

`List` monad 是 `Maybe` monad 的一般形式，即结果可能失败（`[]`），也有可能有**多种结果**。

```haskell
instance Monad [] where
  return x = [x]
  xs >>= f = concatMap f xs
  fail _ = []
```

因此 `List` monad 的 `>>=` 是用 `concatMap` 定义的：`f x` 可能会产生多种结果，而 `>>=` 会将每个元素产生的结果收集起来，并展平。

`List` monad 的 do notation 语法与列表闭包非常像：

```haskell
plus :: Num b => [b] -> [b] -> [b]
plus xs ys = do
  x <- xs
  y <- ys
  return (x + y)

> plus [1,2,3] [4,5,6]
[5,6,7,6,7,8,7,8,9]
```

类似的，`List` 的函数也可以用 do notation 来写：

```haskell
map' :: (a -> b) -> [a] -> [b]
map' = \f -> \xs -> do
  x <- xs;
  return (f x)

filter' :: (a -> Bool) -> [a] -> [a]
filter' = \p -> xs -> do
  x <- xs;
  if p x then [p] else []
```

# Functor，Applicative 与 Monad 的关系

## `join` 函数

数学上通过 `fmap`、`return` 与 `join` 定义 monad，这种定义与 Haskell 中的定义是等价的：

```haskell
join :: m (m a) -> m a
join mma = mma >>= id
-- ma >>= f = join $ fmap f ma
```

其中，`join` 用于拆包，在数学上满足以下定律：
- `join . return = id = join . fmap return`
- `join . join = join . fmap join`

上面两个定律的左端是先脱掉外层的 `m`，再脱内层的 `m`；右端则恰好相反，先脱内层的 `m`，再脱外层的 `m`。

但是 `return . join /= id`，例如 `return . join [[1, 2], [3,4]] = [[1, 2, 3, 4]]`，中间的信息已经丢失了。除非是特殊的 monad，例如 `Identity` monad。

## Monad 与 Applicative 的关系

Monad 一定是 functor 和 applicative。因此可以用 monad 实现 functor 和 applicative。

```haskell
fm :: Monad m => (a -> b) -> m a -> m b
fm f ma = ma >>= \a -> return (f a)

ap :: Monad m => m (a -> b) -> m a -> m b
ap mab ma = do
  f <- mab
  a <- ma
  return $ f a
```

实际上，`return = pure`，因此 monad 和 applicative 的区别在于 `join` 函数。

```haskell
class Applicative f where
  pure :: a -> f a                   -- 来自 Pointed
  fmap :: (a -> b) -> f a -> f b     -- 来自 Functor
  (<*>) :: f (a -> b) -> f a -> f b

class Monad m where
  return :: a -> m a                 -- 来自 Pointed，等价于 pure
  fmap :: (a -> b) -> m a -> m b     -- 来自 Functor
  (<*>) :: f (a -> b) -> m a -> m b  -- 来自 Applicative
  join :: m (m a) -> m a
```

得益于 `join` 函数，monad 可以将**前面某一步**的值用于**后续某一步**运算中（即 `>>=` 操作）：
- 先用 `fmap` 将容器内的值进行运算得到 `m a -> m t a`
- 然后用 `join` **将外层的包装去掉** `m t a -> t a`
- 如果没有 `join`，则无法完成第二步操作，因而也不能在第一步用 `fmap`

在 applicative 中，`<*> :: f (a -> b) -> f a -> f b`，只能将参数传入函数中，并等参数全部传入后得到这个函数的结果，而不能让第二个参数“使用”第一个参数的值。

```haskell
> [x + y | x <- [1..3], y <- [1..x]]
[2,3,4,4,5,6]

> [1..3] >>= \x -> [1..x] >>= \y -> return (x + y)
[2,3,4,4,5,6]

> (+) <$> [1..3] <*> [1..x]
<interactive>:21:30: Not in scope: 'x'
```

即 applicative 的计算过程是上下文无关的；而 monad 的计算过程可以是上下文相关的。

## 从 `Pointed` 到 `Monad`

由上面所讲的可知 `Functor` 是 `Applicative` 的超集，`Applicative` 是 `Monad` 的超集。但是实际上可以从更加简单的 `Pointed` 开始构建这个关系：

```haskell
class Pointed f where
  point :: a -> f a
```

显然，`point = pure = return`，这样的函数成为 injection map。

而 `Functor` 提供了 `fmap`，结合两者可以得到 `Applicative`，因而形成这样一条依赖链：`(Pointed, Functor) => Applicative => Monad`。

## AMP

AMP 即 Functor-Applicative-Monad Proposal。在一开始，人们并没有意识到 monad 是 applicative 的子集（Monad 在 90 年代引入，Applicative 在 2006 年引入）。因此导致许多 applicative 上的函数无法应用在 monad 中。

因此在 GHC 7.8 中重新定义了这个关系，使得 `Functor => Applicative => Monad`。

由于这个原因，标准库中有许多函数是重复定义的：
- `fmap`，`liftA`，`liftM`
- `forM`，`mapM`，`traverse`
- `sequence`，`sequenceA`
- `ap`，`<*>`
- 甚至 `Alternative` 和 `MonadPlus` 也是重复定义的

在实现一个类型时，可以先实现 `Monad` 和 `Alternative`，然后直接用 `pure = return` 和 `(<*>) = ap` 来导出 `Applicative` 和 `MonadPlus`。

## Applicative Do

开启 `ApplicativeDo` 扩展后，就可以用 do notation 来写 applicative 了：

```haskell
\m -> do { x <- m; return (not x) }
-- 推断结果为 Functor f => f Bool -> f Bool

\a b -> do {a' <- a ; b' <- b; return (a', b')}
-- 推断结果为 Applicative f => f t1 -> f t -> f (t1, t)
```

使用 applicative do 有两个好处：
- 代码更加清晰直观
- 让编译器自动推断限定到底是在 Functor 上，Applicative 上还是 Monad 上

> 从 applicative do notation 中也不难看出 functor, applicative 和 monad 的区别：
> - functor 只能用 `<-` 拆一次，然后用掉
> - applicative 可以拆多次，但是只能在最后一次 `return` 里面用（即运算是上下文无关的）
> - monad 可以拆多次，并且前面的结果可以在中间用，也可以最后用（运算可以是上下文相关的）
