---
layout: "post"
title: "「Haskell 学习」 11 Arrow"
subtitle: "Category & Arrow"
author: "roife"
date: 2022-11-26

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags", "Arrow@函数式编程", "函数反应式编程@函数式编程"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# `Arrow`

## `Category` typeclass

Category typeclass 可以看成是“函数组合”到“态射”的推广，推广了 `id`（自己和自己连接）和 `(.)`（头尾连接）运算，即“可以组合但是无法应用的函数”。

前面介绍的 `Functor`、`Applicative`、`Monad` 都可以看成是 object，而 `Category` 则是对 morphism 的抽象。

```haskell
infixr 9 .

class Category cat where
  id :: cat a a
  (.) :: cat b c -> cat a b -> cat a c
  {-# MINIMAL id, (.) #-}
```

并且需要满足单位元和结合律：
- Right identity: `f . id = f`
- Left identity: `id . f = f`
- Associativity: `f . (g . h) = (f . g) . h`

其中，`cat a b` 表示 `a ~> b`。例如当 `cat` 为 `->` 时，`cat a b` 就是 `a -> b`：

```haskell
instance Category (->) where
  id = GHC.Base.id
  (.) = (GHC.Base..)
```

在 `Category` 中还定义了 `>>>` 和 `<<<`：

```haskell
infixr 1 >>>, <<<

(>>>) :: Category cat => cat a b -> cat b c -> cat a c
(>>>) = flip (.)

(<<<) :: Category cat => cat b c -> cat a b -> cat a c
(<<<) = .
```

其中 `>>>` 满足结合律：`f >>> (g >>> h) = (f >>> g) >>> h`。

## `Arrow`

`Arrow` 基于 `Category` 对计算（computation）的一种抽象。但是 `Arrow` 在 `Category` 上添加了：
- 函数到 `Arrow` 的转换（`arr`）
- 对二元元组的操作，即部分应用操作（`***`）。

`Arrow` 很像 `Applicative` 和 `Monad`，但是前者的定义同时包含了“输入类型”和“返回类型”（`Arrow :: (* -> * -> *) -> Constraint`），而后者的定义中只包含了“返回类型”（`Monad :: (* -> *) -> Constraint`）。

```haskell
infixr 3 ***
infixr 3 &&&

class Category arrow => Arrow arrow where
  arr :: (b -> c) -> arrow b c

  first :: arrow b c -> arrow (b, d) (c, d)
  first = (*** id)

  second :: arrow b c -> arrow (d, b) (d, c)
  second f = arr swap >>> first f >>> arr swap
    where
      swap :: (x, y) -> (y, x)
      swap ~(x, y) = (y, x)

  (***) :: arrow b c -> arrow b' c' -> arrow (b, b') (c, c')
  f *** g = first f >>> second g

  (&&&) :: arrow b c -> arrow b c' -> arrow b (c, c')
  f &&& g = arr (\b -> (b, b)) >>> (f *** g)

  {-# MINIMAL arr, (first | (***)) #-}
```

- `arr` 可以将一个普通的函数转换为 `Arrow`，类似 `lift` 操作
- `first` 和 `second` 表示把两种类型间的计算变换成对两种类型组成的元组的计算
- `f *** g` 和 `f &&& g` 可以组合两个 `arrow`，将计算转换为对元组的计算

![Arrow-first-second](/img/in-post/post-haskell/arrow-first-second.png){:height="500px" width="500px"}

另一个常用的函数是 `dup`：

```haskell
dup :: Arrow arrow => arrow a (a, a)
dup = arr $ \a -> (a, a)
-- dup = arr $ (,) <*> id
```

此外，`Arrow` 还定义了其它用于组合计算的运算符：

```haskell
(^<<) :: Arrow a => (c -> d) -> a b c -> a b d
f ^<< a = arr f <<< a

(<<^) :: Arrow a => a c d -> (b -> c) -> a b d
a <<^ f = a <<< arr f

(>>^) :: Arrow a => a b c -> (c -> d) -> a b d
a >>^ f = a >>> arr f

(^>>) :: Arrow a => (b -> c) -> a c d -> a b d
f ^>> a = arr f >>> a
```

### Arrow laws

- `arr id = id`（`arr Prelude.id = Control.Category.id`）
- `arr (f >>> g) = arr f >>> arr g`
- `arr id >>> f = f`
- `f >>> arr id = f`
- `first (arr f) = arr (first f)`
- `first (f >>> g) = first f >>> first g`
- `first f >>> arr fst = arr fst >>> f`
- `first f >>> arr (second g) = arr (second g) >>> first f`
- `first (first f) >>> arr assoc = arr assoc >>> first f`
  - `assoc ((a, b), c) = (a, (b, c))`

### `Arrow` instances

#### `(->)`

`(->)` 是一个 pure `Arrow`：

```haskell
instance Category (->) where
  id = Prelude.id
  (.) = (Prelude..)

instance Arrow (->) where
  arr f = f
  (***) f g (x, y) = (f x, g y)
  first f = f *** id
  second f = id *** f
```

利用 `Arrow (->)`，可以很方便地将两个类型间的函数转换为对应元组上的函数。

#### `Kleisli`

`Kleisli` 可以将 monad 相关的计算转换为 `Arrow`。

```haskell
newtype Kleisli m a b = Kleisli { runKleisli :: a -> m b }

instance Monad m => Category (Kleisli m) where
  -- id :: Kleisli m a a
  id = Kleisli return

  -- (.) :: Kleisli m b c -> Kleisli m a b -> Kleisli m a c
  Kleisli f . Kleisli g = Kleisli (g >=> f)

instance Monad m => Arrow (Kleisli m) where
  -- arr :: (b -> c) -> Kleisli m b c
  arr f = Kleisli (return . f)

  -- first :: Kleisli m b c -> Kleisli m (b, d) (c, d)
  first (Kleisli f) = Kleisli $ \(a, c) -> do
    b <- f a
    return (b, c)
```

#### 其它的 `Arrow` 实例

- 自动机：`newtype Auto b c = Auto (b -> (c, Auto b c))`
- Static arrow：`Applicative F => F (b -> c)`
- Stream transformers：`Stream b -> Stream c`

# `ArrowApply`

`ArrowApply` 是 `Arrow` 的一个子类，它定义了 `app` 函数来“应用”一个 `Arrow`：

```haskell
class Arrow arrow => ArrowApply arrow where
  app :: arrow (arrow b c, b) c
```

从类型可以看出，这个 arrow 输入是一个可应用的元组 `(arrow b c, b)`（第一个元素是一个 `b` 到 `c` 的计算，第二个元素是其输入 `b`），输出是 `c`。

实际上，实现了 `ArrowApply` 的 arrow 等价于**允许柯里化**的运算：

$$
\operatorname{\mathtt{Arrow}}\ (b, c)\ d \cong b \rightarrow \operatorname{\mathtt{Arrow}}\ c\ d
$$

如果一个类型可以实现 `ArrowApply` 类型类那么它也可以实现 `Monad`，反之亦然。二者是等价的，因为根据柯里化，有

$$
\operatorname{\mathtt{Arrow}}\ b\ c \cong \operatorname{\mathtt{Arrow}}\ (b, ())\ c \cong b \rightarrow \operatorname{\mathtt{Arrow}}\ ()\ c \cong b \rightarrow M\ c
$$

## `(->)` 是 `ArrowApply`

显然 `(->)` 是一个 `ArrowApply`：

```haskell
instance ArrowApply (->) where
  app = uncurry ($)
  -- app (f, x) = f x
```

## `ArrowApply` laws

- Composition: `arr (first (>>> h)) >>> app = app >>> h`
- Reduction: `arr (first mkPair) >>> app = arr id`
  + `mkPair :: Arrow arrow => b -> arrow c (b, c)`
  + `mkPair b = arr $ \c -> (b, c)`
- Extensionality: `mkPair f >>> app = f`

此处 `mkPair` 用于构造元组。

# `ArrowChoice`

`ArrowChoice` 是 `Arrow` 的一个子类，它定义了 `+++` 函数来处理 `Either` 类型，使得 `Arrow` 能够实现“分支选择”：

```haskell
class Arrow a => ArrowChoice a where
  left :: a b c -> a (Either b d) (Either c d)
  left = (+++ id)

  right :: a b c -> a (Either d b) (Either d c)
  right = (id +++)

  (+++) :: a b c -> a b' c' -> a (Either b b') (Either c c')
  f +++ g = left f >>> arr mirror >>> left g >>> arr mirror
    where
      mirror :: Either x y -> Either y x
      mirror (Left x) = Right x
      mirror (Right y) = Left y

  (|||) :: a b d -> a c d -> a (Either b c) d
  f ||| g = f +++ g >>> arr untag
    where
      untag (Left x) = x
      untag (Right y) = y

  {-# MINIMAL (left | (+++)) #-}
```

- `+++` 对于 `Either` 的两种情况分别应用不同的函数
- `left` 与 `right` 函数会根据输入进行“选择性执行”
  + 当输入为 `Left` 时才应用 `left` 的参数 `f`
  + 当输入为 `Right` 时才应用 `right` 的参数 `f`
- `|||` 是特化的 `+++`，要求两个 `Arrow` 的输出类型相同，输入类型可以不同

![ArrowChoice](/img/in-post/post-haskell/arrow-choice.png){:height="600px" width="600px"}

```haskell
foo = ((+ 10) +++ (const "Fail")) >>> (id ||| (const 0))

-- > foo $ Left 10
-- 20
-- > foo $ Right "Cheated"
-- 0
```

## 与 `Arrow` 的关系

不难发现，`left` 与 `first`、`right` 与 `second`、`(+++)` 与 `***`、`(|||)` 与 `(&&&)` 是相对应的。实际上它们之间互为对偶关系。`Arrow` 对应了 product type，`ArrowChoice` 对应了 sum type。

Product type 和 sum type 有分配关系：

```haskell
distr :: (Either a b, c) -> Either (a, c) (b, c)
distr (Left a, c) = Left (a, c)
distr (Right b, c) = Right (b, c)
```

因此 `Arrow` 的函数与 `ArrowChoice` 的函数满足分配律：`first (left f) >>> arr distr = arr distr >>> left (first f)`

## `ArrowChoice` laws

- `left (arr f) = arr (left f)`
- `left (f >>> g) = left f >>> left g`
- `f >>> arr Left = arr Left >>> left f`
- `left f >>> arr (id +++ g) = arr (id +++ g) >>> left f`
- `left (left f) >>> arr assocsum = arr assocsum >>> left f`
  + `assocsum (Left (Left x)) = Left x`
  + `assocsum (Left (Right y)) = Right (Left y)`
  + `assocsum (Right z) = Right (Right z)`

## `(->)` 是 `ArrowChoice`

```haskell
either :: (a -> c) -> (b -> c) -> Either a b -> c

instance ArrowChoice (->) where
  -- left f = f +++ id
  -- right f = id +++ f
  f +++ g = (Left . f) ||| (Right . g)
  (|||) = either
```

即根据输入类型应用不同的函数。

# `ArrowLoop`

`ArrowLoop` 是 `Arrow` 的一个子类，它定义了 `loop` 函数，使得 `Arrow` 能够实现“循环”：

```haskell
class Arrow a => ArrowLoop a where
  loop :: a (b, d) (c, d) -> a b c
```

![ArrowLoop](/img/in-post/post-haskell/arrow-loop.png){:height="200px" width="200px"}

## `ArrowLoop` laws

- Extension: `loop (arr f) = arr (\b -> fst (fix(\(c, d) -> f(b, d))))`
- Left tightening: `loop (first h >>> f) = h >>> loop f`
- Right tightening: `loop (f >>> first h) = loop f >>> h`
- Sliding: `loop (f >>> arr (second k)) = loop (arr (second k) >>> f)`
- Vanishing: `loop (loop f) = loop (arr unassoc >>> f >>> arr assoc)`
    + `unassoc (a, (b, c)) = ((a, b), c)`
    + `assoc ((a, b), c) = (a, (b, c))`
- Superposing: `second (loop f) = loop (arr assoc >>> second f >>> arr unassoc)`

## `(->)` 是 `ArrowLoop`

`(->)` 对应的 `loop` 函数又被称为 `trace` 函数。

```haskell
instance ArrowLoop (->) where
  -- ((b,d) -> (c,d)) -> b -> c
  loop f b = let (c, d) = f (b, d) in c
```

下面通过斐波那契数列的例子来解释 `ArrayLoop`：

```haskell
fibOnce :: (Int -> Int) -> Int -> Int
fibOnce f 0 = 1
fibOnce f 1 = 1
fibOnce f n = f (n - 1) + f (n - 2)

fib :: Int -> Int
fib = loop (second fibOnce >>> arr (\(n, f) -> (f n, f)))
-- fib = fibOnce fib
```

此处 `fib` 的定义展开后得 `let (c, d) = (fibOnce d b, fibOnce d) in c`。其中 `d = fibOnce d`，即递归定义的 `fib`。

不难发现，对于 `loop (second g >>> arr (\(n, f) -> (f n, f)))`，最后都能得到 `let (x, f) = (g f b, g f) in x`，从而进行递归，其本质也是一个不动点。

## `ArrowCircuit`

使用 `ArrowCircuit` 可以为 `ArrowLoop` 提供一个初始值，在一些情况下会用到：

```haskell
class ArrowLoop a => ArrowCircuit a where
  delay :: b -> a b b
```

### Causal Communitive Arrows

如果 `ArrowCircuit` 满足下面两条定律，则称为 causal communitive arrows（CCA）：
- `delay i *** delay j = delay (i, j)`
- `first f >>> second g = second g >>> first f`

对于 CCA，并行的两个运算交换以后结果不变，互相没有影响，因此满足 `f *** g = (g *** f) >>> arr swap`。

# Arrow notation

Arrow notation 类似于 do notation，能用命令式的方式组合 arrow。

## `proc...do` 与 `-<`

`proc p -> f -< a` 会被翻译为 `arr (\p -> a) >>> f`，其中：
- `proc` 后面跟着一个后面用到的变量（类似于 λ 表达式，可以是 `(a, b)` 这种 pattern）
- `f -< a` 相当于 `f a`，`a` 中可以使用 `p`
- 表达式的含义为传入 `p`，并计算出 `f a`

对于中间变量，也可以使用 `proc p -> do { p' <- f -< a }`，它会被翻译为 `(first (proc p -> f -< a)) >>> proc(p', p) -> do { B }`：
- 在第一个通道中计算 `f a`，结果命名为 `p'`（同样可以是 pattern）
- 第二个通道为原始传入的 `p`，可以在后面使用

如果中间出现了多个需要保存的中间变量，则都以元组的形式保存在第二个通道中。

例如：

```haskell
proc x -> do
  y <- f -< x + 1
  g -< 2 * y
  let z = x + y
  t <- h -< x * z
  returnA -< t + z

-- 等价于
arr (\x -> (x + 1, x)) >>>
  first f >>>
  arr (\(y, x) -> (2 * y, (x, y))) >>>
  first g >>>
  arr (\(_, (x, y)) -> let z = x + y in (x * z, z)) >>>
  first h >>>
  arr (\(t, z) -> t + z)
```

上面的例子的 `returnA` 定义如下：

```haskell
returnA :: Arrow a => (b -> c) -> a b c
returnA = arr . id
```

## `-<<` 与 `ArrowApply`

在 `proc p -> f -< x` 中，如果 `f` 中用到了 `p` 中的变量，那么生成的 `arr (\p -> a) >>> f` 就不再正确了，因此 `p` 只能在 `a` 中使用。这种情况对应了 `ArrowApply`（应用管道中的函数）。

对于 `ArrowApply`，可以使用 `-<<` 来代替 `-<`，`proc p -> f -<< x` 会被翻译成 `arr (\p -> (f, a)) >>> app`：

```haskell
proc x -> f x -<< x+1

-- 等价于
arr (\x -> (f x, x+1)) >>> app
```

## `ArrowChoice`

如果在 arrow notation 中使用 `if ... then ... else`，那么就会被翻译成 `ArrowChoice`，其中两种情况分别翻译为 `left` 和 `right`，并且在后续使用 `ArrowChoice` 来对两种情况进行不同的处理。

```haskell
proc (x, y) ->
  if f x y
  then g -< x+1
  else h -< y+2

-- 等价于
arr (\(x, y) -> if f x y then Left x else Right y) >>>
        (arr (\x -> x + 1) >>> f) ||| (arr (\y -> y + 2) >>> g)
```

此外，在 `proc` 中还可以使用 `case`：

```haskell
case input of
  [] -> f -< ()
  [x] -> g -< x+1
  x1:x2:xs -> do
    y <- h -< (x1, x2)
    ys <- k -< xs
    returnA -< y:ys
```

## `rec` 与 `ArrowLoop`

在语句前使用 `rec` 可以实现定义 `ArrowLoop`。

`proc p -> do { rec A; B}` 会被翻译成：

```haskell
second (loop (proc (p, pA) -> do { A; idA -< (pB, pA) })) >>>
  proc(p, pB) -> do { B }
```

例如：

```haskell
fib :: Integer -> Integer
fib = proc n -> do
  rec f <- fibOnce -< f
  returnA -< f n
```

# 信号函数 `SF`

信号函数 `SF` 可以对一串信号进行处理，写成函数的形式为 `[a] -> [b]`，其中要求 `length [a] = length [b]`，即等价于 `map`。其定义如下：

```haskell
newtype SF a b = SF {runSF :: [a] -> [b]}

-- 实现 Category
instance Category SF where
  id = SF (Prelude.id)
  (.) (SF f) (SF g) = SF ((Prelude..) f g)

-- 实现 Arrow
-- > runSF (arr (+1)) [1..10]
-- [2..11]
instance Arrow SF where
  arr f = SF (map f)
  -- f :: [b] -> [c]
  -- bd :: [(b, d)]
  -- 结果为 :: [(c, d)]
  first (SF f) = SF $ \bd ->
    let (bs, ds) = unzip bd
    in zip (f bs) ds

-- 实现 ArrowChoice
instance ArrowChoice SF where
  left (SF f) = SF (\xs -> combine xs (f [y | Left y <- xs]))
    where combine (Left y:xs) (z:zs) = Left z: combine xs zs
          combine (Right y:xs) zs = Right y: combine xs zs
          combine [] zs = []


-- 实现 ArrowLoop
instance ArrowLoop SF where
  -- f  :: [(b, d)] -> [(c, d)]
  -- as :: [b]
  loop (SF f) =
    SF $ \as ->
      let (bs, cs) = unzip (f (zip as (stream cs)))
      in bs
    where
      stream ~(x:xs) = x : stream xs

-- 实现 ArrowCircuit
instance ArrowCircuit SF where
  delay x = SF (init . (x:))
```

在定义 `ArrowCircuit` 时，`delay` 只是把一个信号放在了列表的最前面。同时为了保证输入与输出列表的长度相等，需要用 `init` 去掉输出的最后一个元素。

## 数字信号处理

数字信号序列可以用 `[Bool]` 来表示，而对数字信号变换的过程可以用 `SF` 来描述。例如求信号序列的上升沿：

```haskell
risenEdge :: SF Bool Bool
risenEdge = arr id &&& delay False >>> arr detect
  where
    detect (a, b) = a && not b

-- 相当于 \l -> map (\(a, b) -> a && not b) (zip l (False : init l))
-- > showBools $ runSF risenEdge [True, True, False, True, False]
-- [True, False, False, True, False]
```

还可以用 arrow notation 来表示：

```haskell
risenEdge' :: SF Bool Bool
risenEdge' = proc b -> do
  c <- delay False -< b
  returnA -< b && not c
```

这种表示非常像数字电路的描述：`b` 是当前信号的寄存器，`c` 是 `delay` 之后的信号的寄存器，而 `b && not c` 则对应了一段组合逻辑。

类似的，通过 `ArrowLoop` 还可以实现锁存器：

```haskell
flipflop :: SF (Bool, Bool) (Bool, Bool)
flipflop = proc (R, S) -> do
    -- 初始状态为 set
    rec Q <- delay False -< nor R Q'
        Q' <- delay True -< nor S Q
    returnA -< (c, d)
  where nor a b = not (a || b)

-- 对应的语句为（初始的 Q 与 Q' 需要惰性匹配）
loop (arr (\((R, S), ~(Q, Q')) -> ((S, Q'), (R, Q))) >>>
      nor *** nor >>>
      delay (False, True) >>>
      arr id &&& arr id)
```

![Arrow Flip-flop](/img/in-post/post-haskell/arrow-flip-flop.png){:height="200px" width="200px"}

此外，还可以实现一个简单的 Counter：

![Arrow Counter](/img/in-post/post-haskell/arrow-counter.png){:height="400px" width="400px"}

```haskell
counter :: ArrowCircuit a ⇒ a Bool Int
counter = proc reset -> do
    rec output <- returnA -< if reset then 0 else next
        next <- delay 0 -< output + 1
    idA -< output

-- 对应的语句为
counter' = loop (arr (\(reset, next) -> dup (if reset then 0 else next)) >>>
                 (first (arr (+1) >>> delay 1) >>> aswap))
```

# `ArrowZero` 与 `ArrowPlus`

`ArrowZero` 与 `ArrowPlus` 对应 `Monad` 中的 `MonadPlus`（即 `Alternative`）。同时实现二者的 arrow 是一个 monoid。

```haskell
class Arrow a => ArrowZero a where
  zeroArrow :: a b c
class ArrowZero a => ArrowPlus a where
  (<+>) :: a b c -> a b c -> a b c
```

例如 Kleisli arrow 就是一个 monoid：

```haskell
instance MonadPlus m => ArrowZero (Kleisli m) where
  zeroArrow = Kleisli (\_ -> mzero)

instance MonadPlus m => ArrowPlus (Kleisli m) where
  Kleisli f <+> Kleisli g = Kleisli (\x -> f x `mplus` g x)
```
