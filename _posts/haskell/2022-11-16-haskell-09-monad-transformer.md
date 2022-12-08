---
layout: "post"
title: "「Haskell 学习」 09 Monad Transformer 与 MTL-style"
subtitle: "组合不同的 Monad"
author: "roife"
date: 2022-11-16

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags", "Monad@函数式编程"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# Monad Transformer

Monad tranformer 可以组合多种 monad，以产生新的行为。通常某种 monad `m` 对应的转换器为 `mT`。

## `IdentityT`

`IdentityT` 是 `Identity` monad 的转换器，它的定义如下：

```haskell
-- newtype Identity a = Identity { runIdentity :: a } deriving (Functor)
newtype IdentityT m a = IdentityT { runIdentityT :: m a } deriving (Functor)

instance (Monad m) => Monad (IdentityT m) where
  return = IdentityT . return
  ima >>= k = IdentityT $ do
    a <- runIdentityT ima -- runIdentityT m :: m a
    runIdentityT (k a)    -- k :: a -> IdentityT m b

instance (Monad m) => Applicative (IdentityT m) where
  pure = return
  (<*>) = ap
```

`IdentityT` 的类型为 `(* -> *) -> * -> *`。从定义和 `>>=` 可以看出，`IdentityT m` 相当于在 `Identity` 内部多加了一层 `m`，并不增加原来的功能，且得到的 monad 与原 monad 同构，比较 trivial：

$$\operatorname{\mathtt{IdentityT}}\ \operatorname{\mathtt{m}} \cong \operatorname{\mathtt{m}} \cong \operatorname{\mathtt{mT}}\ \operatorname{\mathtt{Identity}}$$

事实上 `Writer`、`Reader` 和 `State` 都是利用 monad transformer 定义的，例如：

```haskell
type State s = StateT s Identity
```

## `MaybeT`

```haskell
-- data Maybe a = Nothing | Just a
data MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) } deriving (Functor)

instance Monad m => Monad (MaybeT m) where
  return x = MaybeT $ return (Just x)
  MaybeT a >>= f = MaybeT $ do
    result <- a
    case result of
      Nothing -> return Nothing
      Just x -> runMaybeT (f x)

instance (Monad m) => Applicative (MaybeT m) where
  pure = return
  (<*>) = ap
```

`MaybeT` 与 `Maybe` 的差别在于 `MaybeT` 外面多套了一层 `m`。`MaybeT` 和原来的 `Maybe` 差别不大，只是有了组合 monad 的能力。

## `StateT`

```haskell
-- newtype State s a = State { runState :: s -> (a, s) }
newtype StateT s m a = StateT { runStateT :: s -> m (a, s) } deriving (Functor)

instance (Monad m) => Monad (StateT s m) where
  return x = StateT $ \s -> return (x, s)
  StateT h >>= f = StateT $ \s -> do
    (a, newState) <- h s
    runStateT (f a) newState

instance (Monad m) => Applicative (StateT s m) where
  pure = return
  (<*>) = ap
```

`StateT` 和 `State` 有着比较大的差距，其定义并不是 `s -> (m a, s)`，而是 `s -> m (a, s)`，因此表现出来的行为也不一样。

例如分别使用 `State` 和 `StateT` 嵌套 `Maybe`：
- `runState $ State s (Maybe a) :: s -> (Maybe a, s)`：计算失败时状态 `s` 能保留下来，即 `(Nothing, s)`
- `runStateT $ StateT s Maybe a :: s -> Maybe (a, s)`：计算失败时，状态 `s` 会被丢弃，即 `Nothing`

### `WriterT`

```haskell
newtype WriterT w m a = WriterT { runWriterT :: m (a, w) } deriving (Functor)

instance (Monoid w, Monad m) => Applicative (WriterT w m) where
  pure = return
  (<*>) = ap

instance (Monoid w, Monad m) => Monad (WriterT w m) where
  return a = WriterT $ return (a, mempty)
  m >>= k = WriterT $ do
    (a, w) <- runWriterT m
    (b, w') <- runWriterT (k a)
    return (b, w `mappend` w')
```

# MonadT 与嵌套 monad

以 `Maybe` 嵌套 `State` 为例，如果想在计算失败时保留状态，那么有两种写法：`MaybeT (State s a)` 和 `State s (Maybe a)`。

在使用时，嵌套 monad 需要更加繁琐的模式匹配：

```haskell
-- MaybeT (State s a)
stackM :: MaybeT (State s) a
stackM = do
  push 5
  a <- pop
  return $ a + 1

-- State s (Maybe a)
stack :: State [Int] (Maybe Int)
stack = do
  push 5
  a <- pop
  case a of
    Nothing -> return Nothing
    Just a  -> return $ Just $ a+1
```

在嵌套 monad 时，每次从 monad 中取出一个值内层 monad 相关的副作用（effect）；而使用了 monad transformer 后，`MaybeT` 在 `>>=` 的定义中直接处理了，相当于 **monad transformer 自动处理了组合 monad 时的副作用**（不难发现对嵌套 `Maybe` 的模式匹配处理与 `MaybeT` 定义中的模式匹配处理是一样的，相当于把处理过程放到了定义里）。因此使用 monad 转换器来组合要更为方便。

# MonadT 的组合顺序

相同的 monad transformer 如果以不同方式组合，其行为也会有所不同。例如组合 `State` 与 `Maybe`，可以组合出两种：
- `runStateT $ StateT s Maybe a :: s -> Maybe (a, s)`
- `runMaybeT $ State s a :: s -> (Maybe a, s)`

由比如 `Writer` 和 `State` 组合，可以组合出两种：
- `runStateT $ StateT s (Writer w) a :: (\s -> (a, s), w)`
- `runWriterT $ WriterT w (State s) a :: \s -> ((a, w), s)`

在 `State` 与 `Monad` 的组合中，两种组合顺序会影响组合出来的 monad 的效果（因为 `Maybe` 中可能得到两种 constructor）；而在 `Writer` 和 `State` 中，两种组合顺序组合出来的 monad 同构，因为 $s \rightarrow ((a, w), s) \cong s \rightarrow ((a, s), w) \cong s \rightarrow (a, s, w)$。

同时不难发现，多个 monad transformer 组合起来时，其行为类似于一个栈，最外层的 monad transformer 的作用效果在最里层，例如 `StateT s (WriterT w Maybe) a` 可以得到 `\s -> Maybe ((a, s), w)`。

# `MonadTrans` 与 `lift`

## `MonadTrans` typeclass

Monad 可以主动与 monad transformer 组合，组合的方式与对应的 monad transformer 的副作用有关。这种组合的能力可以用 `MonadTrans` typeclass 描述。其中的 `lift` 函数可以在 monad 外面套一层 monad transformer（即让 monad transformer 的效果作用在 monad 内部）。

```haskell
class MonadTrans t where
  lift :: Monad m => m a -> t m a
```

例如 `State` monad 的定义：

```haskell
instance MonadTrans (StateT s) where
  lift m = StateT $ \s -> do
    a <- m
    return (a, s)

push :: Int -> State [Int] ()
push x = state $ \xs -> ((), x : xs)

pushMS :: Int -> MaybeT (State [Int]) ()
pushMS x = lift $ push x
```

`lift` 需要满足下面的定律：
- `lift . return = return`
- `lift (m >>= f) = lift m >>= (lift . f)`

如果 `<-` 操作作用在 `m a` 上取出来的是 `a`，那么 `<-` 作用在 `lift (m a)`（即 `mT m a`）上取出来的仍然是 `a`。

## `liftIO` 与 `MonadIO`

如果 monad transformers 组合得到的 monad 有 IO 行为，那么 `IO` 一定在最里层，因为没有 `IO` transformers。因此对于提升 `IO -> mT1 mT2 ... mTn IO`，Haskell 定义了一个 `liftIO` 操作，能够一步直接将 `IO` 提升到最里层，即 `liftIO f = lift $ lift $ ... $ lift f`。

```haskell
class (Monad m) => MonadIO m where
  liftIO :: IO a -> m a
```

`liftIO` 是通过递归的：首先 `IO` 能实现 `MonadIO`。然后对于任意一个 transformer `mTi` 定义了 `MonadIO m => MonadIO (mTi m)`。因此可以自动进行转换 `IO a => mT1 (IO a) => mT2 (mT1 (IO a)) => mTn (... (mT2 (mT1 (IO a))))`。

```haskell
MonadIO IO
MonadIO m => MonadIO (IdentityT m)
MonadIO m => MonadIO (ListT m)
...
```

另外需要注意的一点是，由于 `IO` 一定在最里层，因此其副作用一定作用于最外层。例如 `MaybeT (WriterT [String] IO) a :: IO ((Maybe a, [String]))`。

## `liftBase` 与 `MonadBase`

实际上，`liftIO` 是完全依靠 Haskell 的类型系统进行推断，因此在 `transformers-base` package 中定义了 `MonadBase` typeclass，用于抽象这种一步提升的行为。

```haskell
class (Monad b, Monad m) => MonadBase b m | m -> b where
  liftBase :: b a -> m a
```

这里 `m` 是多层类型 `mT m`，`b` 是里层类型 `m`。`m -> b` 表示知道了 `mT m` 就能推出 `m`（因为就是剥掉最外面一层）。

这个 typeclass 的实现和 `MonadIO` 一样，是递归定义的：

```haskell
instance MonadBase [] []
instance MonadBase IO IO
instance MonadBase Maybe Maybe
...

instance MonadBase b m => MonadBase b (ListT m)
instance MonadBase b m => MonadBase b (MaybeT m)
instance MonadBase b m => MonadBase b (IdentityT m)
...
```

这样就可以用 `liftBase` 来代替 `lift` 了。

# 一个简单的 HTML 解析器

这里定义一个支持解析 CFG 的 Parser，将 HTML 解析成 AST。

```
<html>
  <head>Hello world!</head>
  <body>Hello again!</body>
</html>
```

```haskell
Tag "html" [
  Tag "head" [Text "Hello world!"],
  Tag "body" [Text "Hello again!"]
]
```

```haskell
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Char

data Node = Tag String [Node]
          | Text String
           deriving (Show,Eq)

xml :: String
xml = "<html><head>Hello world!</head><body>Hello again!</body></html>"

-- Parser a :: String -> Maybe (a, String)
type Parser a = StateT String Maybe a

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = StateT $ \str ->
  case str of
    [] -> Nothing
    s:ss -> if p s then Just (s, ss) else Nothing

char :: Char -> Parser Char
char c = satisfy (==c)

letter = satisfy isAlpha

string str = mapM char str

runParser :: Parser a -> String -> Maybe (a, String)
runParser = runStateT

textNode :: Parser Node
textNode = fmap Text $ some $ satisfy (/= '<')

tagNode :: Parser Node
tagNode = do
  tagName <- char '<' *> many letter <* char '>'
  subNode <- many $ tagNode <|> textNode
  string "</" >> string tagName >> char '>'
  return $ Tag tagName subNode

-- > runParser tagNode xml
-- Just (Tag "html" [Tag "head" [Text "Hello world!"],Tag "body" [Text "Hello again!"]], "")
```

# MTL-style

类似于 `MonadState` 这种使用 typeclasses 来抽象 monad 行为（或者通常称为 effects）的风格通常称为 MTL-style。

就像在命令式编程中通常推荐使用 interface 来代替 class 一样，MTL-style 规定了 monad 的行为，但是不约束具体的实现。因此更加推荐使用 MTL-style 的写法，而非写明确的 monad/monadT。

MTL-style 有下面几个优点：
- 可以不用明确地写 `lift`（上面的 `MonadBase` 就是 MTL-style 的写法，可以让 Haskell 自动推断 `lift` 的数量）
- MTL-style 的写法通用性更强：例如 `MonadState s` 可以是 `State s`，也可以是 `MaybeT (State s)`

## `MonadWriter`

`MonadWriter` 是 `Writer` 的 mtl-style 版本，如果 monad `m` 中使用了 monoid `w` 进行记录，那么 `m` 的行为就和 `Writer` 一样。

它提供了三个函数：
- `tell`：添加一条日志
- `listen`：返回一个元组 `(结果, 本次产生的日志)`
- `pass`：传入一个带有 `(结果, 函数)` 的 `Writer`，返回结果，并将此 `Writer` 的日志用函数**映射后记录下来**

```haskell
class (Monoid w, Monad m) => MonadWriter w m | m -> w where
  tell   :: w -> m ()
  listen :: m a -> m (a, w)         -- 说明 listen 的返回结果是 (a, w)
  pass   :: m (a, w -> w) -> m a

instance MonadWriter String (Writer String) where
  writer (a, w) = Writer (a, w)
  listen m = let (a, w) = runWriter m in writer ((a, w), w) -- 此处 (a, w) 是计算的结果
  pass m = let ((a, f), w) = runWriter m in writer (a, f w)
```

此外，还有两个常用函数：
- `listens :: (MonadWriter w m) => (w -> w) -> m a -> m (a, w)`
  + 传入一个函数和 `Writer`，返回一个元组 `(结果, 映射后的日志)`，而日志原样记录
- `censor :: (MonadWriter w m) => (w -> w) -> m a -> m a`
  + 传入一个函数和 `Writer`，只返回结果，但是记录下的是映射后的日志（更方便的 `pass`）

```haskell
listens :: (MonadWriter w m) => (w -> w) -> m a -> m (a, w)
listens f m = do
  (a, w) <- listen m
  return (a, f w)

censor :: (MonadWriter w m) => (w -> w) -> m a -> m a
censor f m = pass $ do
  a <- m
  return (a, f)
```

## `MonadReader`

`MonadReader` 是 `Reader` 的 mtl-style 版本，如果 monad `m` 中可以从环境 `r` 中读取值，那么 `m` 的行为就和 `Reader` 一样。

它提供了两个函数：
- `ask`：直接返回环境
- `local`：传入一个函数和 `Reader`，读取前会先用函数进行映射，然后用传入的 `Reader` 读取映射后的新环境
  + 之所以叫 `local` 是因为它不会改变环境，改变的环境只会在这次读取用

```haskell
class Monad m => MonadReader r m | m -> r where
  ask   :: m r
  local :: (r -> r) -> m a -> m a

instance MonadReader r (Reader r) where
  ask = Reader id
  local f m = Reader $ runReader m . f
```

此外，标准库内还提供了 `withReader` 与 `mapReader`：
- `withReader`：类似 `local`，但是它可以改变读取环境的类型
- `mapReader`：类似 `local`，会先读再映射

```haskell
withReader :: (r' -> r) -> Reader r a -> Reader r' a
withReader f m = Reader $ runReader m . f

mapReader :: (a -> b) -> Reader r a -> Reader r b
mapReader f m = Reader $ f . runReader m
```

## `MonadState`

`MonadState` 对应 `State`，包含两个函数：
- `get`：获取当前状态
- `put`：更新状态

```haskell
class (Monad m) => MonadState s m | m -> s where
  get :: m s
  put :: s -> m ()

instance MonadState s (State s) where
  get   = state $ \s -> (s, s)
  put s = state $ \_ -> ((), s)
```

`State` monad 可以实现 `MonadReader` 与 `MonadWriter`：

```haskell
instance (MonadReader r m) => MonadReader r (StateT s m) where
  ask = lift ask
  local f (StateT g) = StateT $ \s -> local f (g s)

instance (Monoid w, MonadWriter w m) => MonadWriter w (StateT s m) where
  tell = lift . tell
  listen (StateT f) = StateT $ \s -> do
    ((a, s'), w) <- listen (f s)
    return ((a, w), s')
  pass (StateT f) = StateT $ \s -> do
    ((a, f'), s') <- f s
    pass (return (a, s'), f')
```
