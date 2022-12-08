---
layout: "post"
title: "「Haskell 学习」 08 IO Monad 与 State Monad"
subtitle: "Monad 与副作用操作"
author: "roife"
date: 2022-11-15

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags", "Monad@函数式编程"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# `IO` monad

`IO` monad 能够改变系统的状态，即 `IO a = OS_State -> (a, OS_State)`。

Haskell 中的输入输出都用 `IO` 进行表达，例如：
- `getChar :: IO Char` / `getLine`
- `putChar :: Char -> IO ()` / `putStr` / `putStrLn`

其他的和系统相关的操作（不仅限于 IO）也都放在 `IO` 中，例如环境变量的读写、文件读写、和操作系统的交互等，这样就可以保证修改是按照一定顺序执行的（由 monad 的性质）。使用 `IO` monad 可以把会改变系统状态的操作与其他函数分离开来，在 `IO` 中的操作都可能有副作用。

在 Haskell 中，所有 `IO` 的 constructor 都是私有的（因此不能用模式匹配），不通过 monad 就无法取出 `IO` 中的值（以 `IO` 作为输入，那么 `>>=` 就只能以 `IO` 作为返回结果），因此也**无法构造 `IO` 到非 `IO` 的函数**（例如 `IO String -> String`），即**无法从非纯世界回到纯世界**。即便如此，在两个相邻 `IO` 操作之间的操作仍然是纯的，相当于**将纯函数式操作嵌入了非纯的世界**，由此达到副作用的隔离。例如 Haskell 的 `main` 函数一定会输出，所以 `main` 函数的类型也是 `IO a`，但是可以将无副作用的操作封装成函数，由 `main` 调用。

对于 `IO a`，如果 `a` 的值不被取出，那么这个操作就不会被执行，例如 `const (return ()) $ putStrLn "Bye World"` 就不会输出。

## `IORef`

由于 `IO` 可以表达副作用，在 Haskell 中可以用 `IORef` 来实现变量，其中 `IORef` 类似一个指针，指向一个 `IO` 中的值。

| 函数 | 作用 |
| - | - |
| `newIORef :: a -> IO (IORef a)` | 生成一个 IORef 并存入给定参数 |
| `readIORef :: IORef a -> IO a` | 读取值 |
| `writeIORef :: IORef a -> a -> IO ()` | 写入值 |
| `modifyIORef :: IORef a -> (a -> a) -> IO ()` | 应用函数 |

## Unsafe `IO`

虽然理论上无法从非纯世界返回纯世界，但是 Haskell 还是提供了一些从 `IO` 中读取值的 API。注意，使用这些 API 是十分危险的。

```haskell
unsafePerformIO :: IO a -> a        -- 从 IO 中读取值
unsafeDupablePerformIO :: IO a -> a -- 从 IO 中读取值，但是不进行多线程检查
unsafeInterleaveIO :: IO a -> IO a  -- 延后 IO 操作（可能会破坏运算性质，如交换律）
unsafeFixIO :: (a -> IO a) -> IO a  -- 类似 fixIO，重复执行，但是不进行多线程检查
```

# `State` Monad

`State` monad 和 `IORef` 很像，是一组记录状态的函数，但是 `State` monad 是纯的，不会产生副作用。

## `Writer` Monad

`Writer w a` monad 用于记录日志，它是一个二元组 `(a, w)`，第一个元素是计算的结果，第二个元素是记录的日志。`Writer` monad 的 `>>=` 会将两个 `Writer` 的日志合并。

`Writer` 这个 constructor 是私有的，只能通过 `writer` 来构造。这是因为标准库中的 `Writer` monad 是使用 monad transformer `WriterT` 定义的，所以不存在 `Writer` 这个 constructor，只能通过 `writer` 来构造。

```haskell
newtype Writer w a = Writer { runWriter :: (a, w) } deriving (Functor)

instance (Monoid w) => Monad (Writer w) where
  return x = Writer (x, mempty)
  (Writer (x, v)) >>= f =           -- f :: a -> Writer w b
    let (Writer (y, v')) = f x      -- 计算结果，并得到新日志
    in Writer (y, v `mappend` v')   -- 合并日志

instance Monoid w => Applicative (Writer w) where
  pure = return
  (<*>) = ap
```

注意这里 `Writer` 不是 monad，`Writer w` 才是一个 monad，`Writer :: * -> * -> *`。

```haskell
left' :: Int -> Writer String Int
left' x = Writer (x-1, "left, ")

leftTwice' i = do
  x <- left' i
  y <- left' x
  return y

> runWriter $ leftTwice' 4
(2, "left, left, ")
```

从 do notation 上只能看到计算的结果，记录日志的过程由 `>>=` 的定义隐式地完成了（相当于副作用）。

## `Reader` Monad

`Reader` monad 与 `Writer` monad 恰好相反，可以读取数据，但是不能修改它。与 `Writer` 不同的是，`Reader` 中存的是函数 `r -> a` 而非读出来的值（可以理解为 `Reader` 并不存值，只是存了“读取的方式”）。其中类型 `r` 被称为环境，所以 `Reader` monad 称为 Environment monad。

同样，`Reader` 这个 constructor 是私有的，只能通过 `reader` 来构造。

```haskell
newtype Reader r a = Reader { runReader :: r -> a } deriving (Functor)

instance Monad (Reader r) where
  return a = Reader $ \_ -> a
  m >>= k = Reader $ \r -> runReader (k (runReader m r)) r

instance Applicative (Reader r) where
  pure = return
  (<*>) = ap
```

从 `>>=` 的定义可以看出在整个计算过程中环境都是不变的，但是每层可以从环境中取出值。`>>=` 运算符在给定的环境 `r` 下执行 `m`，并将结果输入函数 `k` 中（即每一层读出来的仍然是 `a`）。

### 用 `Reader` 实现变量查询

这里定义一个简单的 AST：用 `String` 表示变量，用 `Int` 表示变量的值，并且包含了 `Decl` 和 `Add` 用于定义变量和加法运算。

其中，变量的绑定使用元组 `(String, Int)` 表示，而环境 `Env` 则是一个列表 `[Bind]`。

```haskell
import Control.Monad.Reader
import Data.List (lookup)

type Bind = (String, Int)
type Env = [Bind]

data Exp = Val Int
         | Var String
         | Add Exp Exp
         | Decl Bind Exp deriving (Show, Eq)

updateEnv :: Bind -> Env -> Env
updateEnv = (:)
```

下面用 `Reader` 实现 `resolve`，操作，替换一个表达式中所有的变量。

```haskell
resolve :: Exp -> Reader Env (Maybe Exp)
resolve (Val i) = return $ Just $ Val i
resolve (Var s) = do
  env <- ask
  case lookup s env of
    Nothing -> return Nothing
    Just i  -> return $ Just $ Val i
resolve (Add e1 e2) = do
  v1 <- resolve e1
  v2 <- resolve e2
  case (v1, v2) of
    (Just (Val i1), Just (Val i2)) -> return $ Just $ Add v1 v2
    _ -> return Nothing
resolve (Decl b e) = local (updateEnv b) $ resolve e
```

## `State` Monad

`State` monad 能够实现前面两个 monad 的功能，既能记录状态，也能读取状态。`State` monad 中存的是一个 `s -> (a, s)` 的函数而非状态本身，这个函数可以理解为传入一个状态，做一次计算，并产生一个类型为 `a` 的结果和一个新状态，用元组表示成 `(a, s)`。

类似 `Writer` 和 `Reader`，`State` 的 constructor 也是私有的，但是可以用 `state` 来构建。

```haskell
newtype State s a = State { runState :: s -> (a, s) } deriving Functor

instance Monad (State s) where
  return x = State $ \s -> (x, s)

  (>>=) :: State s a -> (a -> State s b) -> State s b
  State h >>= f = State $ \s ->
    let (a, newState) = h s         -- h :: s -> (a, s)
        State g = f a               -- f :: a -> State s b
    in g newState                   -- g :: s -> (b, s)

instance Applicative (State s) where
  pure = return
  (<*>) = ap
```

从 `>>=` 的定义可以看出每次读取出来的是运算结果 `a`，同时每次计算都会有一个新状态 `newState`，并且将新状态用于下一次计算。

### `State` Monad 实现栈

```haskell
import Control.Monad.State

type Stack = [Int]

pop :: State Stack Int
pop = state $ \(x:xs) -> (x, xs)

peek :: State Stack Int
peek = state $ \(x:xs) -> (x, x : xs)

push :: Int -> State Stack ()
push i = state $ \xs -> ((), i : xs)
```

### `State` Monad, `FunApp` Monoid and `Reader` Monad

`State` monad 可以看成是 `FunApp` monoid 和 `Reader` monad 组合而成的。

```haskell
newtype FunApp s   = FunApp { appFunApp :: s -> s }
newtype Reader s a = Reader { runReader :: s -> a }
newtype State s a  = State { runState :: s -> (a, s) }
```

### `RState` Monad

`RState` 又称为 `Backwards state` 或者 `Reversed state`，会先执行右边的计算，再执行左边的计算。

有趣的是，它的 `>>=` 操作符和 `State` 的不同，它将状态首先传入右边的计算，然后利用右边计算得到的状态计算左边；并且右边的计算需要依赖左边的计算结果。这样似乎产生了一个递归，但是由于 Haskell 是惰性求值的，因此在定义时不会产生问题。

```haskell
newtype RState s a = RState { runRState :: s -> (a, s) } deriving Functor

instance Monad (RState s) where
  return x = RState $ \s -> (x, s)
  RState sf >>= f = RState $ \s ->
    let (a, s'') = sf s'
        (b, s') = runRState (f a) s
    in (b, s'')

instance Applicative (RState s) where
  pure = return
  (<*>) = ap

rget :: RState s s
rget = RState $ \s -> (s, s)

rmodify :: (s -> s) -> RState s ()
rmodify f = RState $ \s -> ((), f s)

rput :: s -> RState s ()
rput = rmodify . const

execRState :: RState s a -> s -> s
execRState f s = snd (runRState f s)
```

在惰性求值中，只有一个值被用到的时候才会执行相应的计算。在 `RState` 中，除了最后的 `return` 以外，**后面改变状态时不可以使用前面读取的状态**，否则就会造成递归求解。

下面从 `return`、`rget`、`rmodify` 三条语句展开说明 `RState` 的计算过程：
- 由于惰性计算，且前面没用到 `rget` 的值，因此 `return` 才会用到某个 `rget` 的值，此时它就会尝试求解这个 `rget`
- 求解 `rget` 时需要 `s'`，所以 `rget` 会调用下一条语句 `runRState (f a)` 求**状态** `s'`（`f a` 的 `a` 没有用到，不计算）
- 如果遇到了 `rget`，不受影响；如果中途遇到了某个 `rmodify`
  + 此时如果 `rmodify` 用到了前面某个 `rget` 的值 `a`，那么就会尝试求解这个 `a`，造成死循环（错误）
  + 如果没有用到，那么 `rmodify` 也需要状态 `s'`，类似 `rget`，继续调用后面的语句求**状态**
- 因此无论是 `rmodify` 还是 `rget`，都会到达 `return`，并且只求**状态** `s'`
- 在 `runRState (return a) s` 中，`return` 的状态是 `s`
  + 这个 `s` 是**从第一条语句传来，中途不发生改变，是用户传入的初始状态**
- 得到初始状态后，按照调用的顺序会从后往前执行，因此整个运算是从后往前执行的

```haskell
n = do
  a <- rget
  rput 2
  b <- rget
  return $ a + b

> runRState n 1
(3, 2)
```

## `RWST` monad

`RWST` monad 包含了 `ReaderT`、`WriterT` 和 `StateT` 的操作，在 `Control.Monad.Trans.RWS` 中定义。
