---
layout: "post"
title: "「Haskell 学习」 10 More monads"
subtitle: "Parsec, Free monad 与 Continuation"
author: "roife"
date: 2022-11-16

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags", "Monad@函数式编程", "Parser@编译", "Continuation@函数式编程", "Free monad@函数式编程"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# `Parsec` monad

`Parsec` 是一个专门用于语法解析的 monad，其定义为 `ParsecT s u m a`：
- `s`：输入类型，如字符串
- `u`：用户状态类型，如 `()`，`Int` 等
- `m`：组合的 monad，可以记录状态等，通常可以直接用 `Identity`
- `a`：解析结果类型

`Parsec` 库中有一些常用函数：
- `oneOf`、`noneOf`：查询字符在不在字符串里
- `skipMany`、`skipMany1`：跳过 token
- `lexeme`：忽略 token 后的空格
- ……

在匹配使用 `<|>` 要注意，`Parsec` 如果对第一种情况取了字符，那么就不会尝试第二种解析：

```haskell
test1 = string "(a)" <|> string "(b)"
test2 = try (string "(a)") <|> string "(b)"

-- > parseTest test1 "(b)"
-- parse error at (line 1, column 1): unexpected "b", expecting "(a)"

-- > parseTest test2 "(b)"
-- "(b)"
```

更多细节参考官方文档。

# `Free` monad

此处的 `free` 意为“免费的”，而非“自由的”。因为 `Free` monad 可以将一个 functor 变成一个 monad，即“免费”获得了一个 monad。（但是具体的计算过程依赖于 interpretation，如果这个 functor 无法成为 monad，那么也无法定义出满足 monad 定律的 interpretation）

Free monad 在工程中的作用在于可以将程序（DSL）存进一个数据结构中，并且在上面应用不同的 interpretation，从而达到不同的效果（例如让一段程序在测试时，可以让它每执行一步就打印一个额外的信息，方便测试）。

## Free algebraic structures

在抽象代数中，Free X 一般是指“X 的最简单的结构”，只包含 X 必要的性质，而不包含其他多余的性质。

形式化地来讲，集合 $X$ 上 free structure 包含集合 $F$ 以及伴随的 free structure 运算（操作），并且：
1. 存在一个 embedding $i : X \rightarrow F$
   - Embedding 是一个单射，并且能够保留 $X$ 的结构（即是一个态射）
2. $F$ 是一个由 $i(X)$ 和 free structure 上定义的运算形成的最小闭包（$X$ 是生成集）
3. Free structure 只包含必要的性质（以及可以从必要的性质中推导出来的其他性质）：如果 $F$ 是 $X$ 上的 free object，那么对于任意的 object $G$，给定一个映射 $f : X \rightarrow G$，都可以将其扩展为唯一的态射 $\operatorname{\mathtt{free}} f : F \rightarrow G$

![Free CD](/img/in-post/post-haskell/free-cd.svg){:height="250px" width="250px"}

在范畴论中，使用左伴随函子（left adjoint functor）和遗忘函子（forgetful functor）定义 free structure。

## Free Monoids

例如对于 monoids 来说，所有的 monoid 都要满足两个操作：单位元 `mempty :: a`，运算 `mappend :: a -> a -> a`。并且，所有的 monoid 都要满足以下三条性质：
- Associativity: `(x <> y) <> z = x <> (y <> z)`
- Left identity: `mempty <> x = x`
- Right identity: `x <> mempty = x`

那么一个 free monoid 就要包含上面的两个操作，满足上面三条运算定律，并且不包含多余的运算定律（例如 commutativity）。

### 列表是 free monoid

实际上，（有限的）`F = List X` 就是 `X` 上的一个 free monoid：
- `F :: [X]`
- `i :: X -> F; i x = [x]`
- `mempty = []`，`mappend = (++)`，`F` 是由 `[x]`、`[]` 和 `(++)` 组成的最小闭包
- 列表不包含其他运算性质

```haskell
data [x] = [] | x : [x]   -- this is pseudo code

instance Monoid [x] where
  mempty = []
  mappend = (++)

ins :: x -> [x]
ins x = [x]

free :: Monoid b => (x -> b) -> [x] -> b
free f [] = mempty
free f (x:xs) = f x `mappend` free f xs
-- free f = foldr (\x b -> f x `mappend` b) mempty
```

整数与加法操作则无法构成一个 free monoid，因为它满足交换律，但是交换律不是 monoids 所必需的。

比较意外的是自然数和加法可以构成一个 free monoid。首先，自然数和列表是同构的。其次，虽然自然数满足交换律，但是它的“交换律”本质上是结合律的体现：

$$
n + k = \underbrace{(1 + 1 + \dots + 1)}_{n\ times} + \underbrace{(1 + 1 + \dots + 1)}_{k\ times} = \underbrace{(1 + 1 + \dots + 1)}_{k\ times} + \underbrace{(1 + 1 + \dots + 1)}_{n\ times} = k + n
$$

因此自然数是 $X = \\{1\\}$ 上的 free monoid，其中 `mappend = +`，`mempty = 0`。同时不难发现，在相同的基底 $X$ 上的所有 free monoids 都是和列表同构的。

这里列表相当于一个 AST（线性的），而 `mappend` 和 `mempty` 的选取不同，则相当于使用了不同的 interpreter，可以得到不同的结果。

### Monads

实际上，monads 也是 monoid。

```haskell
class Functor m => Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b
```

其中 monads 需要满足三条运算定律：
- associativity: `(m >>= g) >>= h = m >>= (\x -> g x >>= h)`
- left identity: `return a >>= h = h a`
- right identity: `m >>= return = m`

如果用 Kleisli composition 来改写：

```haskell
(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
f >=> g = \x -> f x >>= g
```

那么这三条规则可以写作：

- associativity: `(f >=> g) >=> h = f >=> (g >=> h)`
- left identity: `return >=> f = f`
- right identity: `f >=> return = f`

因此 monads 是 `Funtor f => a -> f b` 上的 monoids，其中 `mempty = return`，`mappend = >=>`（这里在 functor 上定义，和范畴论中在 endofunctors 上定义同构）。

## Free monads

### 定义

Free monad 的定义如下，和 `List a = Nil | Cons a (List a)` 定义非常像：

```haskell
-- Pure :: a -> Free f a
-- Free :: f (Free f a) -> Free f a
data Free f a = Pure a | Free (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Free g) = Free (fmap f <$> g)

instance Functor f => Monad (Free f) where
  return = Pure

  -- (>>=) :: Free f a -> (a -> Free f b) -> Free f b
  Pure x >>= f = f x
  Free g >>= f = Free ((>>= f) <$> g) -- g :: f (Free f a >>= f)

  -- join :: Free f (Free f a) -> Free f a
  join (Pure x) = x
  join (Free x) = Free $ join <$> x

instance Functor f => Applicative (Free f) where
  pure = return
  (<*>) = ap
```

不难发现 `Pure` 的类型和 `return :: a -> m a` 非常像；`Free` 的类型和 `join :: m (m a) -> m a` 非常像。注意这里 `Free` 的定义是 `Free (f (Free f a))` 而不是 `Free f (Free f a)`。

> 当然这个实现并不高效，Church-encoded free monads 是一个使用时更加高效的实现。在 `Free` 这个库中定义了 `MonadFree` typeclass，其中会 `Pure` 和 `wrap` 函数定义了 free monads。

对于 `Free f a`，有：
- `X :: Functor f => f a`，`F :: Functor f => Free f a`
- `i :: X -> F; i fa = Free (Pure <$> fa)`
- Monad 中的三种运算 `fmap`、`return` 和 `join` 定义如上一节，并且满足 monad 的三条定律

`Free f a` 类似于 `List`，表达了 monad 的一种结构，并且不进行多余的运算。对于某个具体的 monad，可以通过给 `Free f a` 的运算不同的 interpretation 来得到它。

### `liftF` 与 `foldFree`

`Free f a` 的 `ins` 和 `free` 定义如下（这里需要开启 `RankNTypes` 扩展）：

```haskell
data Free f a = Pure a | Free (f (Free f a))

ins :: (Functor f) => f a -> Free f a
ins fa = Free (fmap Pure fa)

free :: (Functor f, Monad g) => (forall a. f a -> g a) ->
                                (forall a. Free f a -> g a)
free f (Pure a)  = return a
free f (Free fa) = join (f (fmap (free f) fa))
-- free f (Free fa) = f fa >>= free f
```

- `ins` 一般写作 `liftF`，可以将一个 functor `f a` 转换到一个 `Free f a`
- `free` 一般写作 `foldFree`，可以将 functor `f a` 到 monad `m a` 的变换，转换成从对应的 `Free f a` 到 `m a` 的变换

### 用 Free monad 构建 monad

在 Haskell 中，monad 是通过 `return` 和 `>>=` 进行构建的。并且都可以写成这样的形式：

```haskell
do
  x1 <- step1
  x2 <- step2
  x3 <- step3
  ...
  xn <- stepn
  return something
```

如果在中间插入一个 `return`，那么根据 `return x >>= f = f x` 可以将其消掉；如果在末尾不加 `return`，那么根据 `m >>= return = m` 可以加上 `return`。因此所有的 do notation 都等价于上面的形式。这里 `stepi = f xi`，`f` 是一个 monad，因此当然也是一个 functor。

类似于 `List`，free monad 可以把上面 Monad 的这种“顺序”式的表达式存储在数据结构 `Free f a` 中：
- `return something` 就是 `Pure something`
- `Free f a = (Free (f (Free (f (... (Free (f (Pure a))))))))` 中，第 `i` 个 `f` 对应 `stepi = f xi`

即：对于某个函子 `stepi = f xi`，对应的 free monad 为 `ins stepi = Free (m (Pure xi))`；对于单位元 `return a`，对应的 free monad 为 `Pure a`。由于 free monad 也定义了 `>>=`，它可以将几个 free monads 组合成一个整体，使用时也可以用 do notation：

![Free monad](/img/in-post/post-haskell/free-monad.png){:height="500px" width="500px"}

通过上面的化简，可以发现 `freei >>= \xi -> freei1` 会将 `freei1` 替换到 `freei` 的内层。

如果 `stepi` 是复杂的 `Free (f (Free f (...)))` 的形式（即由若干函子组成），相当于 `>>=` 不断进入内层，直到最内层（遇到 `Pure a`）。这一点相当于用 `>>=` 构建了一个 monad，并且和另外一个 `>>=` 相拼接，此时 `>>=` 同样会将接在后面的语句放在内层闭包中，二者是一致的。由此，我们发现了 `Free f a` 保留了 monad 最原始的“结构”。

## 实现 `State` monad/构造 DSL

我们这里尝试不实现 `State` 的 monad 结构，而是只实现它的 functor `StateF`，通过 `Free (StateF s) a` 将其实现为 monad。然后定义一套 interpretation 来模仿 `State` monad 的行为。接着，我们会通过 `foldFree`（`free`）函数证明 `Free (StateF s) a` 与 `State s a` 是等价的。在最后，我们将定义的计算过程视为一套 DSL，并尝试给出另一套 interpretation，以验证 `Free (StateF s) a` 的灵活性。

- 首先，我们需要定义 `StateF` 的 functor 结构：

```haskell
-- 定义 StateF
newtype StateF s a = StateF { runStateF :: s -> (a, s) } deriving (Functor)

getF :: StateF s s
getF = StateF $ \s -> (s, s)

putF :: s -> StateF s ()
putF s = StateF $ const ((), s)
```

`StateF` 是一个 functor，这里还定义了两个常用的操作。

- 接下来，我们通过 `Free f a` 将其实现为一个 monad：

```haskell
type State' s a = Free (StateF s) a

get' :: State' s s
get' = liftF getF

put' :: s -> State' s ()
put' = liftF . putF
```

这里通过 `liftF` 将原来 functor 上的函数转换成 monad 上的函数。

- 接下来可以通过上面的定义写一个计算程序，并定义相应的解释函数（interpretation）：

```haskell
-- 一个计算过程
someComputation :: State' Int ()
someComputation = do
  i <- get'
  put' $ i + 1
  pure ()

-- Free (StateF s) a 的 interpretation
runState' :: State' s a -> s -> (a, s)
runState' (Pure x) s = (x, s)
runState' (Free f) s =
  let (m, s') = runStateF f s
  in runState' m s'

-- > runState' someComputation 0
-- ((),1)
```

如果熟悉 `State` 不难发现，这里的 `runState'` 就是 `State` monad 中 `>>=` 和 `return` 的定义。也就是说，我们在这里将上面的程序“解释”为 `State` monad 的行为。

- 然后我们就可以通过 `foldFree` 函数验证 `State' s a` 与 `State s a` 是等价的。

```haskell
-- 首先定义 fromStateF : X -> G
fromStateF :: StateF s a -> State s a
fromStateF (StateF f) = state f

-- > :t foldFree fromStateF someComputation
-- foldFree fromStateF someComputation :: StateT Int Identity ()

-- > runState (foldFree fromStateF someComputation) 0
-- ((),1)
```

通过这样的一段程序，我们验证了可以用 `Free f a` 来实现 monad。

- 最后，我们尝试构造一套新的 interpretation：

```haskell
printState' :: (Show s, Show a) => State' s a -> s -> String
printState' (Pure x) s = "pure (" <> show x <> "," <> show s <> ")"
printState' (Free f) s =
  let (m, s') = runStateF f s
  in "state change " <> show s <> " -> " <> show s' <> "\n"
     <> printState' m s'

-- > :t printState' someComputation 0
-- printState' someComputation 0 :: String

-- > putStrLn $ printState' someComputation 0
-- state change 0 -> 0
-- state change 0 -> 1
-- pure ((),1)
```

# `Continuation` monad

## Continuation 与 CPS

Continuation 指的是这样一个概念：可以认为任何函数调用都有返回值（包括 `()`），并且这个返回值会传给调用点之后的程序使用，调用点之后**所有剩下待执行的部分**被称为 **continuation**。 Continuation 类似于一个回调函数，只不过这个函数没有显式传入被调用方，而是返回时才调用。

而在 CPS（Continuation Passing Style）中，要求通过 continuation 来处理函数的调用与返回，即：必须将调用点之后的程序作为回调函数传入被调用方，被调用方在返回时调用这个回调函数并传入返回值。因此在 CPS 中，每个函数调用都会显式传入一个回调函数。

CPS 相当于显式地将 continuation 传入函数，并通过调用回调函数的方式模拟了函数的调用返回与现场恢复。不难发现，这个过程其实和 do notation 非常像；如果将 do notation desugar，那我们就得到了一个 CPS 的程序。

CPS 变换（CPS Transformation）是指将一个函数转换为 CPS 形式的过程。

```haskell
fact_cps :: (Eq a, Num a) => a -> (a -> r) -> r
fact_cps 0 k = k 1  -- k 是回调函数，即 continuation
fact_cps n k = fact_cps (n-1) (\x -> k (n * x))
-- 回调函数的参数即函数调用的返回值，回调函数中包含了函数返回后需要进行的计算
```

前面介绍 `>>=` 的时候讲过 `>>=` 利用了闭包的嵌套，强制规定了计算的执行顺序。同样，由于 CPS 通过回调函数来模拟函数的调用和返回，因此可以用 CPS 来改变程序执行的顺序：将后执行的部分作为回调函数传给先执行的部分即可。

```haskell
fib_cps :: Int -> (Int -> r) -> r
fib_cps 0 k = k 1
fib_cps 1 k = k 1
fib_cps n k = fib_cps (n-1) (\n1 -> fib_cps (n-2) (\n2 -> k (n1 + n2)))
```

## `Cont` monad

回调函数的形式非常像 monad 的 `>>=` 运算符。在 monad 中，使用 `>>=` 将 context 绑定到另一个函数的参数上；在 CPS 中，函数主动将参数绑定到 continuation 的参数上。因此考虑将 continuation 包在 monad 中使用。

```haskell
f1 a1 (\r1 ->
  f2 r1' (\r2 ->
     ...))
```

Haskell 的 `Cont` monad 在 `Control.Monad.Cont` 中定义，它的定义如下：

```haskell
newtype Cont r a = Cont { runCont :: (a -> r) -> r } deriving Functor

instance Applicative (Cont r) where
  pure a = Cont $ \k -> k a
  -- cab        :: Cont r (a -> b) = ((a -> b) -> r) -> r
  -- ca         :: Cont r a        = (a -> r) -> r
  -- cab <*> ca :: Cont r b        = (b -> r) -> r
  -- kab        :: a -> b
  cab <*> ca = Cont $ \k -> runCont cab (\kab -> runCont ca (\a -> k (kab a)))

instance Monad (Cont r) where
  return = pure
  -- ca         :: Cont r a         = (a -> r) -> r
  -- acb        :: a -> Cont r b    = a -> ((b -> r) -> r))
  -- ca >>= acb :: Cont r b         = (b -> r) -> r
  -- k          :: b -> r           = \b -> k b
  ca >>= acb = Cont $ \k -> runCont ca (\a -> runCont (acb a) k)
```

此处的 `r` 是回调函数的返回值，取决于回调函数，在真正被调用时才知道，因此在定义 `Cont` monad 时使用一个类型参数表示。

下面解释一下这个定义：
- `Cont` monad 的计算实际上可以两步，对于 `runCont ca k`：第一步执行本函数的计算，第二步调用回调函数 `k`
- `pure` 和 `return`：直接主动调用回调函数 `k` 并传入参数 `a`
- `<*>`：只会作用于第一步计算，用于将 `a1, ..., an` 传入 `a1 -> ... -> b` 得到真正的结果 `b`
  + 计算 `ca` 得到 `a`，然后计算 `cab` 构造需要应用的函数 `kab :: a -> b`
  + 再将 `a` 应用构造出的函数 `kab` 得到结果 `b`，这个 `b` 将被传入真正的 continuation `k`
- `>>=`：主要作用于第二步连接 continuation，将 `acb` 作为 `ca` 的 continuation
  + 先计算 `ca` 得到 `a`，然后将 `a` 传入 `ca` 的 continuation `acb`
  + `acb` 计算完成后，同样需要一个 continuation 进行回调，即后续的 `k`
  + 不难发现，在 do notation 中 `<-` 得到的值即为 `ca` 计算的第一步值 `a`

回调函数 `k` 有两种可能性：
- 如果当前语句后面没有语句了，那么 `k` 是当前函数的回调，即当前函数的 caller 或是（用户主动调用时）传入的函数
- 如果当前语句后面还有语句，那么 `k` 是后面跟着的语句

下面用一个例子来说明：

```haskell
fact_cps :: Int -> Cont r Int
fact_cps 0 = return 1
fact_cps n = do
  n1 <- fact_cps (n - 1)
  return (n * n1)
```

`fact_cps n` 展开可以得到：

```haskell
-- fact_cps n
fact_cps (n - 1) >>= \n1 ->
  return (n * n1)

-- n1 是 fact_cps (n - 1) 的返回值
```

在上面的例子中，`return (n * n1)` 是 `n1 <- fact_cps (n - 1)` 的 continuation；Caller `fact_cps (n + 1)` 或用户主动传入的函数（例如 `show`）是 `return` 的 continuation。

当使用 do notation 来应用 `Cont r a` 时，一条语句后跟着的所有语句都是它的 continuation：

![Continuation monad](/img/in-post/post-haskell/continuation.png){:height="500px" width="500px"}

## `ContT` monad

同样，在 Haskell 中 `Cont` 是通过 monad transformer `ContT r m a` 定义的，即 `ContT r Identity a`。

```haskell
newtype ContT r m a = ContT { runConT :: ((a -> m r) -> m r) } deriving (Functor)

-- 和 Cont 一样
instance (Monad m) => Monad (ContT r m) where
  return a = ContT $ \k -> k a
  ca >>= acb = ContT $ \k -> runContT ca (\a -> runContT (acb a) k)

instance (Monad m) => Applicative (ContT r m) where
  pure = return
  (<*>) = ap
```

例如需要在内部打印

```haskell
fib_cps :: Int -> ContT r IO Int
fib_cps 0 = return 1
fib_cps 1 = return 1
fib_cps n = do
  n2 <- fib_cps (n-2)
  liftIO $ putStrLn $ "fib_cps " ++ show (n-2) ++ "=" ++ show n2
  n1 <- fib_cps (n-1)
  liftIO $ putStrLn $ "fib_cps " ++ show (n-1) ++ "=" ++ show n1
  return (n1 + n2)
```

## `callCC`

在 `Cont` monad 中，回调函数 `k` 是在 `>>=` 中被隐式调用的，无法显式调用。但是利用 `callCC` 可以实现显式使用 `k`：

```haskell
fact_cps1 :: Int -> Cont r Int
fact_cps1 0 = return 1
fact_cps1 n = do
  n1 <- fact_cps1 (n - 1)
  callCC $ \k ->        -- k 是 callCC 的 continuation，这里后面没有语句了，所以是回调函数 k（caller 或用户传入的函数）
    let r = n * n1
    in if r > 10000
         then k 0
         else return r
```

下面是 `callCC` 的定义：

```haskell
class Monad m => MonadCont m where
  callCC :: ((a -> m b) -> m a) -> m a

instance MonadCont (Cont r) where
  callCC :: ((a -> Cont r b) -> Cont r a) -> Cont r a
  callCC f = Cont $ \h -> runCont (f (\a -> Cont $ \_ -> h a)) h
```

`callCC` 的原理是：在 `Cont` monad 中，`>>=` 不会主动调用后面的语句，而是将后面的语句用回调函数 `k` 的形式传给前面的语句。因此 `callCC` 可以通过修改这个 `k` 来忽略部分语句。

其中：
- `h` 是当前 `callCC` 语句的 continuation，即跟在 `callCC` 后面的语句（如果后面没语句，则是当前函数的回调函数）
- `f :: (a -> Cont r b) -> Cont r a` 是 `callCC` 的参数
- `\a -> Cont $ \_ -> h a` 是传入 `f` 的回调函数（即 `f` 内部看到的 `k`），`callCC` 在 `h` 外面“包”了一层
- `f` 计算完得到 `a`，然后将 `a` 传入这个 `k`，得到 `Cont $ \_ -> h a`
  - 此时 **`f` 中**调用 `k` 的语句后面的部分作为 continuation 传入 `k`，但是**被忽略**（`\_`）
  - 因此调用 `k` 相当于忽略后面的语句，即**直接退出 `f`**，直接返回 `h a :: r`
  - 在 `run (f ...) h` 中，`h` 是 `f` 的最后一条语句的 continuation（在最后一条语句的内层），此时一同被忽略
- 如果不调用，则返回最后一行的 `Cont r a`，这种情况相当于 `runCont (f _) h`
  - `h` 作为 `f` 的最后一条语句的 continuation，继续执行，相当于 `f _ >>= h`
  - 因此此处可以用 `k` 也可以用 `return`

下面是一个例子：

```haskell
-- 计算 x * 2 (0 < x < 50)
f :: Int -> Cont r Int
f x = do
  x' <- callCC $ \k -> do
    when (x > 50) $ k 50  -- 必须用 k
    when (x < 0) $ k 0    -- 必须用 k
    return x              -- 也可以用 k x
  return $ x' * 2
```

![CallCC](/img/in-post/post-haskell/callcc.png){:height="500px" width="500px"}

## 使用 `callCC` 实现递归

利用 `callCC` 可以实现任意的控制流。例如下面这个程序里实现了 imperative languages 中的 `goto`。

```haskell
print4 :: ContT r IO ()
print4 = do
  (goto, n) <-                      -- goto :: Int -> ContT r IO ()
    callCC $ \k -> do
      ret <- let f x = k (f, x)     -- 定义函数，而非模式匹配
             in return (f, 0)
      lift $ putStrLn $ "In callCC "
      return ret
  if n < 4 then do
    lift $ putStrLn $ "Before goto " ++ show n
    goto (n + 1)
    lift $ putStrLn $ "After goto " ++ show n
  else return ()                    -- return () :: ContT r IO ()

-- (runContT print1) print
-- In callCC
-- Before goto 0
-- Before goto 1
-- Before goto 2
-- Before goto 3
-- ()
```

其中 `f x = k (f x)` 类似于 `fix` 函数，利用了 Haskell 的 lazy evaluation 避免在定义时死循环。
- 一开始 `(goto, n) = (f, 0)`，其中 `goto = f :: ContT r IO ()` 是 lazy 的
  - 遇到 `goto` 时 Haskell 会尝试求值 `(f, 0)` 中的 `f`
  - 根据定义知 `f x = k (f x)`，会继续调用 continuation，并且 `(goto, n) = (f, 4)`
- 一直重复这个过程直到调用 `return ()`，此时不再用 `goto`，返回一个 `ContT r IO ()`

值得注意的是此处 `f` 的定义：

```haskell
f x = k (f, x)
    = (\a -> Cont $ \_ -> h a) (f, x)
    = Cont $ \_ -> h (f, x)
```

即 `f = \x -> Cont $ \_ -> h (f, x)`。其中 `_` 是**调用点之后的 continuation**（而不是 `callCC` 内部的定义点之后，因为在 `callCC` 内部只是定义了，并没有使用），直接被忽略。`h` 是 `callCC` 后面的 continuation，会在 `goto` 中被执行。

![callCC-recursion](/img/in-post/post-haskell/callcc-recursion.png){:height="500px" width="500px"}
