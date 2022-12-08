---
layout: "post"
title: "「Haskell 学习」 04 Data types and kinds"
subtitle: "数据类型"
author: "roife"
date: 2022-11-11

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 数据类型定义

## 用 `data` 定义类型

### Constructor

```haskell
data T = cons1 type1 type2 ... typen
       | ...
       | consm type1' type2' ...
         [deriving ...]
```

其中 `cons1`，……`consm` 是 **constructor**，`typeX` 是一个具体的类型。Constructor 加上对应类型的变量就构成了类型 `T`。例如

```haskell
data MaybeInt = Just Int | Nothing
```

Constructor 本身也可以看作一个函数，类型为 `type1 -> type2 -> ... -> typen -> T`。

### 访问类型变量

一般来说，访问类型变量需要模式匹配。

```haskell
just :: MaybeInt a -> a
just (Just a) = a
just Nothing = error "Not a Just"
```

此时有一些简化的写法：

- 直接定义访问器：

```haskell
data MaybeInt a = Just { runJust :: a } | Nothing
-- runJust (Just 5) = 5
-- :t runJust :: MaybeInt a -> a
```

- 用 `@` 指代模式匹配中被拆开的数据：

```haskell
f :: MaybeInt a -> ...
f m@(Just a) = -- 可以用 m 表示传入的 MaybeInt a
```

- 只需要访问、修改部分数据时，直接用对应的访问器访问、修改：

```haskell
-- m :: Just 5

incM :: MaybeInt a -> MaybeInt a
incM m = m { runJust = 1 + (runJust m) } -- Just 6

-- 或者
incM (Just {runJust = a}) = Just (a + 1)
```

### `deriving`

利用 `deriving` 关键字可以让 Haskell 自动导出一些函数，例如：

```haskell
data Day = Mon | Tue | Wed | Thu | Fri | Sat | Sun
  deriving (Show, Eq, Ord, Enum, Read)
```

### Unit 类型

```haskell
data () = () -- Haskell 嵌入的语法,我们无法定义
```

## 参数化类型

如果某个构造器的某个类型变量不确定，可以将其作为类型的参数。

```haskell
data Maybe a = Just a | Nothing
```

### Type constructor

`Maybe` 这种带参数的类型，称为 **type constructor**。

**Type constructor 和 Constructor 可以同名。**

### 元组 constructor

元组的构造器为 `(,)` 或 `(,,)` 等。

开启 `TupleSections` 扩展后，可以用元组的构造器来 partial evaluation。

```haskell
> :t (, , 5)
(, , 5) :: Num t2 => t -> t1 -> (t, t1, t2)
```

### 函数 constructor

函数类型的构造器为 `(->)`。

```haskell
data (->) a b
```

## 递归类型

例如自然数定义：

```haskell
data Nat = Zero | Succ Nat
  deriving (Show, Eq, Ord)
```

## `newtype`

用 `newtype` 可以定义**只有 constructor**且**constructor 有且仅有一个参数**的类型。但是**类型本身可以有多个参数**。

```haskell
newtype T a b = NewType (a, b)
```

`newtype` 适用于了给某个已有的类型加一层包装来表示区分，并且不希望像 `data` 一样给类型检查增加运行时开销（即不检查 $\bot$）。

`newtype` 和 `type` 是有区别的：前者定义了新类型，与原来的类型不兼容；后者只是定义了别名。

由于 `newtype` 只是定义了一层包装，因此可以用 `GeneralizedNewtypeDeriving` 扩展让 Haskell 通过 `deriving` 自动导出包装类型已经有的 typeclasses。

```haskell
newtype Velocity = Velocity Int deriving (Num, Show, Eq)

> Velocity 5 + Velocity 10
Velocity 15
```

# 表达式的语言扩展

## Multi-way if

用 `MultiWayIf` 可以让 `if` 支持多条件语句。

```haskell
-- guard 对应的 if 和缩进有关
foo a1 a2 =
    if | guard1 -> if | guard2 -> expr2
                      | guard3 -> expr3
       | guard4 -> expr4
       | guard5 -> expr5
```

也可以用大括号包裹。

```haskell
foo a1 a2 =
    if { | guard1 -> if { | guard2 -> expr2 ;
                          | guard3 -> expr3 }
         | guard4 -> expr4 ;
         | guard5 -> expr5 }
```

例如

```haskell
foo a1 a2 =
    if | a1 > 10 -> if | a1 < 10 && a2 > 50 -> True
                       | a1 >= 10 && a2 < 30 -> False
       | a1 < 10 -> True
       | otherwise -> False
```

## Pattern guard

用 `PatternGuards` 扩展可以让模式匹配附加条件判断：`pattern | guard`。

```haskell
data Shape = Circle Int

isValidShape (Circle r) | r > 0 = True
isValidShape _ = False
```

## View pattern

开启 `ViewPattern` 扩展后，可以在模式中应用“单参数函数”并直接对结果进行匹配。`f -> v` 表示对这个位置的参数使用函数 `f` 得到 `v`。

```haskell
match :: Seq Int -> Seq Int -> (Int, Seq Int)
match s1 s2 =
  case viewl s1 of
    EmptyL ->
      case viewr s2 of
        EmptyR -> (0, s2)
        xs :> x -> (x, xs)
    a :< as ->
      case viewr s2 of
        EmptyR -> (a, as)
        xs :> x -> (a + x, xs >< as)

-- 可以直接写成
match' (viewl -> EmptyL) s2@(viewr -> EmptyR) = (0, s2)
match' (viewl -> EmptyL) (viewr -> xs :> x) = (x, xs)
match' (viewl -> a :< as) (viewr -> EmptyR) = (a, as)
match' (viewl -> a :< as) (viewr -> xs :> x) = (a + x, xs >< as)
```

## Pattern synonyms

开启 `PatternSynonyms` 后就可以用 `pattern` 关键字来定义模式的别名了。

```haskell
data Exp = Val Int | Exp String [Exp]

pattern Add t1 t2 = Exp "+" [t1,t2]

eval (Val n) = n
eval (Add t1 t2) = eval t1 + eval t2

foo (Val n) = n
foo (Add t1 t2) = ...
```

# 常用数据结构

## 树

- 二叉树的定义：

```haskell
data Tree a = Leaf | Node a (Tree a) (Tree a)

-- 或者定义成
data Tree a = Leaf a | Node (Tree a) (Tree a)
```

- Rose tree：可以有多叉或者没有叉

```haskell
data Tree a = Node a [Tree a]
```

Haskell 的 `Data.Tree` 中定义的也是 rose tree。

```haskell
data Tree a = Node {
  rootLabel :: a,
  subForest :: Forest a
}
type Forest a = [Tree a]
```

## Zipper

Zipper 能够在容器中反复来回遍历，原理是将已经遍历过的值、当前的值、将要遍历的值都存在 Zipper 中，并且采用合适的变换保持数据结构。

- 列表的 Zipper 定义：

```haskell
data Zipper a = Zipper [a] a [a] deriving Show

fromList :: [a] -> Zipper a
fromList (x:xs) = Zipper [] x xs
fromList _ = error "empty!"
```

- 二叉树的 Zipper 定义：

```haskell
data Tree a = Leaf a | Node a (Tree a) (Tree a)
data Accumulate a =
  Empty
  | L (Accumulate a) a (Tree a)
  | R (Accumulate a) a (Tree a)

type Zipper a = (Tree a, Accumulate a)

right, left, up :: Zipper a -> Zipper a

right (Node n l r, a) = (r, R a n l)
right a = a

left (Node n l r, a) = (l, L a n r)
left a = a

up (t, R a n l) = (Node n l t, a)
up (t, L a n r) = (Node n t r, a)
up z@(t, Empty) = z
```

`Accumulate` 还可以定义是一个列表，二者同构：

```haskell
data Tree a = Leaf a | Node a (Tree a) (Tree a)
data Branch a = R a (Tree a) | L a (Tree a)

type Zipper a = (Tree a, [Branch a])

right, left, up :: Zipper a -> Zipper a

right (Node n l r, t) = (r, R n l : t)
right z@(Leaf a, t) = z

left (Node n l r, t) = (l, L n r : t)
left z@(Leaf a, t) = z

up (r, (R n l:t)) = (Node n l r, t)
up (l, (L n r:t)) = (Node n l r, t)
up z@(t, []) = z
```

# GADT

## GADT

开启 `GADTs` 扩展后，就可以在定义 ADT 时声明每个 constructor 的类型了（之前是编译器自动推导），格式如下：

```haskell
data TypeName a1 a2 ... where
  Con1 :: Type1
  Con2 :: Type2
  ...
```

例如 GADT 定义的 `Maybe`：

```haskell
data Mayba a where
  Nothing :: Maybe a
  Just :: a -> Maybe a
```

## Phantom type

Phantom type 指的是在类型参数中出现，但是没有在 constructor 中作为参数的类型。

结合 GADT 和 Phantom type 可以为 constructor 添加更多类型信息和限制，例如：

```haskell
-- 可能会推导出错误表达式的定义，例如 Add ValBool ValInt
data Exp =
  ValInt Int
  | ValBool Bool
  | Add Exp Exp
  | Equa Exp Exp
  deriving (Eq, Show)

-- a 是 Phantom type，用于限定类型的推导
data Exp a where
  ValInt :: Int -> Exp Int
  ValBool :: Bool -> Exp Bool
  Add :: Exp Int -> Exp Int -> Exp Int
  Equa :: Exp Int -> Exp Int -> Exp Bool
```

# kind

类型的类型称为 **kind**，`*` 是一个 nullary type constructor 的 kind。

```haskell
> :k Maybe
Maybe :: * -> *
> :k Maybe Int
Maybe Int :: *

-- data Triple a b c = Triple a b
> :k Triple
Triple :: * -> * -> * -> *
> :t Triple
Triple :: a -> b -> Triple a b c
-- 注意上面两个 Triple 一个是类型 constructor，一个是普通 constructor，只是同名了
```

## Higher order kinds

Kind 类似于函数，也可以有高阶 kind。

```haskell
data P a = P (a, a)
data BTree a = BLeaf a | BNode (P (BTree a)) deriving (Show, Eq)
data RoseTree a = RLeaf a | RNode [RoseTree a] deriving (Show, Eq)

-- 抽象出一个抽象树
data AbsTree k a = Leaf a | Node (k (AbsTree k a))
-- BTree a = AbsTree P a
-- RoseTree a = AbsTree [] a

> :k AbsTree
AbsTree :: (* -> *) -> * -> *
```

## Constraint kind

在 GHC 中，typeclasses 被统一定义为 **constraint kind**。因此可以用 `:k` 在 GHCi 中查看 typeclasses 的 kind 了。

```haskell
> :k Functor
Functor :: (* -> *) -> Constraint
```

## 在类型定义中声明 kind

开启 `KindSignatures` 扩展后，就可以在定义类型时声明它的 kind。

```haskell
-- 当然这里还要开启 GADTs
data T :: * -> * where
  NIL :: T a
  CONS :: a -> T a -> T a
```

## 为具体类型实现 typeclasses（特例化）

开启 `FlexibleInstances` 扩展后就能为某个具体类型实现 typeclasses 了。此外，`FlexibleInstances` 开启时会同时开启 `TypeSynonymInstances` 扩展，允许为类型别名实现 typeclasses（开启 `TypeSynonymInstances` 后也会自动开启 `FlexibleInstances`）。

```haskell
data Tree :: (* -> *) -> * -> * where
  L :: a -> Tree k a
  N :: k (Tree k a) -> Tree k a

type RoseTree a = Tree [] a
instance Show a => Show (RoseTree a) where
  show (L a) = show a
  show (N tree) = show tree
```

## 定义 kind

开启 `DataKinds` 扩展后，就可以自定义一个 Kind，语法类似于定义 `data`，只不过成员是类型：

```haskell
-- 定义出一个空安全的列表，如果对空列表进行 `safeHead` 操作，则会在编译期报错
-- KEmpty 是 kind
data Empty
data NonEmpty
data KEmpty = Empty | NonEmpty

data List :: * -> KEmpty -> * where
  Nil :: List a Empty
  Cons :: a -> List a b -> List a NonEmpty
```

这里用 `KEmpty` 限制了第二个类型必须是 `Empty | NonEmpty`，称为 data kind。
