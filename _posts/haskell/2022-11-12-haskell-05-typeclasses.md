---
layout: "post"
title: "「Haskell 学习」 05 Typeclasses"
subtitle: "Typeclasses 的定义与实现"
author: "roife"
date: 2022-11-12

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 定义 Typeclasses

通过 `class` 关键字可以定义一个新的 typeclass，一般 typeclass 的名字以大写开头，后面跟着的类型参数用小写。：

```haskell
class C a where
  fun = ...
```

## 使用多个类型参数

开启 `MultiParamTypeClasses` 扩展后，就可以在定义时使用多个类型参数：

```haskell
class C a b ... where
  fun = ...
```

此外，开启了 `MultiParamTypeClasses` 后还可以定义零参数的 typeclasses。事实上，零参数的 typeclasses 和直接用 `data` 定义一个类型没有区别（实际上 Haskell 就是这么实现的）：

```haskell
class OSConfig where
  os_address :: String
  os_user :: String

instance OSConfig where
  os_address = "192.168.0.2"
  os_name = "Song"
```

## 函数声明

在定义 typeclasses 时，可以只给出函数的类型声明，也可以同时给出具体实现。

并且如果几个函数之间有关系，那么可以定义成互相调用的形式，然后使用 `{-# MINIMAL #-}` 来告诉用户最少要实现几个函数：

```haskell
class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool
  x == y = not (x /= y)
  x /= y = not (x == y)
  {-# MINIMAL (==) | (/=) #-}
  -- 至少需要实现 (==) 或 (/=) 中的一个
  -- 要求实现多个可以用 , 分割，例如 {-# MINIMAL minBound, maxBound #-}
```

## 给 typeclasses 添加依赖

在定义 typeclasses 时，可以用 `=>` 天添加依赖（也是 ad-hoc polymorphism）：

```haskell
class (Eq a) => Ord a where
  ...
```

在实现一个 typeclass 前，必须实现它依赖的 typeclasses。

但是注意 typeclasses 间的依赖不能成环。

# 实现 typeclasses

## `instance`

实现 `instance` 关键字可以实现 typeclasses：

```haskell
instance C T where
  func = ...

-- 也可以加上大括号写成 instance C T where { func = ... }
```

并且也可以用 ad-hoc polymorphism 来为特定的类型实现 typeclasses：

```haskell
instance (Eq m) => Eq (Maybe m) where
  Just x == Just y = x == y
  Nothing == Nothing = True
  _ == _ = False
```

## `deriving`

用 `deriving` 关键字可以让 Haskell 自动导出一些 typeclasses：

| 名称          | 所在模块           | 所需语言扩展         |
|---------------|--------------------|----------------------|
| `Functor`     | `Data.Functor`     | `DeriveFunctor`      |
| `Foldable`    | `Data.Foldable`    | `DeriveFoldable`     |
| `Traversable` | `Data.Traversable` | `DeriveTraversable`  |
| `Typeable`    | `Data.Typeable`    | `DeriveDataTypeable` |
| `Data`        | `Data.Data`        | `DeriveDataTypeable` |
| `Generic`     | `GHC.Generics`     | `DeriveGeneric`      |

除此之外不用开启扩展也可以导出 `Eq`、`Ord`、`Enum`、`Ix`、`Bounded`、`Read` 与 `Show`。

### （导出）默认实现

如果 typeclass 定义中给出了默认实现，那么 `instance` 时就不用额外实现了，只需要用 `instance` 声明。

开启 `DericeAnyClass` 扩展后，对于这种有默认实现的类，可以直接用 `deriving` 导出。

```haskell
class DefaultShow a where
  defaultShow :: a -> String
  defaultShow _ = "default"

data Person = P String Int
instance DefaultShow Person

-- 开启 DeriveAnyClass
data Person = P String Int deriving DefaultShow
```

### 为 `newtype` 导出实现

开启 `GeneralizedNewtypeDeriving` 扩展后，可以自动导出 `newtype` 的实现，当然这要求内部包裹的类型已经实现了对应的 typeclasses。

```haskell
newtype P a b = P (a,b) deriving (Show, Functor, Applicative)
```

### 与实现分离的 `deriving`

一些情况下 `deriving` 和类型实现不能写在一起（例如写在不同模块），此时可以开启 `StandaloneDeriving` 扩展，来单独导出 typeclasses。

```haskell
-- A.hs
module A where
data Foo a = Foo a

-- B.hs
{-# LANGUAGE StandaloneDeriving #-}
module B where
import A

deriving instance (Show a) => Show (Foo a)
```

### 控制 `deriving` 策略

不同的扩展可能会引起 `deriving` 的冲突，因此 GHC 引入了新关键字来控制 `deriving` 的策略。

- `stock` 表示导出的 Haskell 2010 中规定的 typeclasses，如 `Eq`
- `newtype` 表示应用 `GeneralizedNewtypeDeriving`
- `anyclass` 表示应用 `DeriveAnyClass`

```haskell
newtype T a = T a
  deriving Show  -- 没有规定，根据 deriving 策略算法决定
  deriving stock (Eq, Foldable)
  deriving newtype Ord
  deriving anyclass Read

deriving stock instance Functor T
```

## 特例化的类型实现/特例化的限制

在 04 中提过，可以开启 `FlexibleInstance` 来为某个特例化的类型实现 typeclass：`instance Eq (Shape Double)`

开启 `FlexibleContexts` 后则可以给 constraint 添加更多的限制。例如使用 `Eq (a, a)` 而非 `Eq a`（相当于特例化的限制）。

```haskell
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

data Shape a = Circle a | Square a | Rectangle a a

instance Eq (Shape Double) -- 只需要FlexibleInstances
instance Eq (a, a) => Eq (Shape (a, a)) -- 同时需要两个扩展
```

## 为类型别名（`type`）实现 typeclasses

默认情况下，类型别名不能实现 typeclasses。但是开启 `TypeSynonymInstances` 扩展后就可以为别名创建实现了（`FlexibleInstance` 和 `TypeSynonymInstances` 开启一个也会开启另一个）。

```haskell
class ToInt i where
  toInt :: i -> Int

type P = Int

instance ToInt P where
  toInt p = p
```

# 类型依赖

##  添加类型依赖

在多类型参数的 typeclasses 中，如果其中的一个类型参数作为函数的返回值，那么此时会产生歧义：

```haskell
class Fun a b where
  fun :: a -> b

instance Fun Int Nat where
  fun a = Zero

instance Fun Int Int where
  fun _ = 0
```

此时必须要用 `(fun 5)::Int`。因为当某个类型参数只作为函数返回值时，仅通过参数，编译器不知道对应的 typeclass 是哪一个。

但是如果返回类型 `RetT` 唯一由参数类型 `{ArgT1, ArgT2, ..., ArgTn}` 决定，那么可以通过声明类型依赖来让 GHC 根据已有的实现自动推导类型。这种关系称为 **functional dependency**（类似于数据库中的函数依赖理论）。

使用类型依赖需要开启 `FunctionalDependencies` 扩展。

```haskell
class Fun a b | a -> b where
  fun :: a -> b
```

如果声明了依赖后仍然存在歧义（比如上面的例子里面 `a` 不能决定 `b`），那么编译器会直接报冲突。

## 通过类型依赖添加限定

类型依赖除了能让编译器自动推导返回参数外，还能用来给 typeclasses 的类型参数添加限制。

例如对于一个特殊的 typeclass `Extract`。它的第一个参数是一个 container，例如 `[a]`，第二个参数是 `a`，并且要求前者是后者的容器。

```haskell
-- 下面的例子都要开启 FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies
class Collection container elem | container -> elem where
  empty :: container -> elem
  insert :: elem -> container -> container

instance Collection [a] a where
  empty _ = []
  insert x xs = x::xs
```

如果没有类型依赖，`extract` 的返回值都是不清楚的。添加依赖 `container -> elem` 相当于告诉编译器 `container` 决定了一个唯一的 `elem`，不仅可以让编译器根据 `instance` 推导出 `empty [1, 2]` 的类型为 `[Int]`，还能够让编译器拒绝 `insert 1 (insert 'c' empty)` 这样的调用

这是因为根据 `instance` 的实现以及类型依赖的限定，`insert _ [Char]` 的类型只能是 `insert Char [Char]`，因此 `insert Int [Char]` 是不合法的。

# Type families

开启 `TypeFamilies` 扩展后，可以定义一个类型的关联类型（Associated type）。

```haskell
class (Num a, Num b) => Plus a b where
  -- a, b -> SumType
  type SumType a b :: *
  plus :: a -> b -> SumType a b
```

关联类型也能表达类型的依赖（即关联的类型依赖于所有的类型参数），可以用于限定类型的实现：

```haskell
class Collection ce where
  type Element ce :: *
  empty :: ce

instance Eq a => Collection [a] where
  type Element [a] = a
  empty = []

-- 这里重定义了 Collection [a] 的 Element 类型，会报错
instance Eq a => Collection [a] where
  type Element [a] = Int
  empty = []
```

# 运行时重载

用 Haskell 的 typeclasses 可以模拟 OO 语言中的 interface。

```haskell
class HasArea t where
  area :: t -> Double

-- 类型 Rect
data Rect = Rect Double Double

instance HasArea Rect where
  area (Rect a b) = a * b

-- 类型 Circle
data Circle = Circle Double

instance HasArea Circle where
  area (Circle r) = pi * r * r
```

利用 GADT 定义一个新类型，只允许实现了 `HasArea` 的类型调用，可以将上面两个类型用同一个类型进行包装，并且可以一起装到容器中，实现多态。

```haskell
-- 需要开启 GADTs
data Shape where
  Shape :: HasArea t => t -> Shape

instance HasArea Shape where
  area (Shape shape) = area shape

> shapes = [Shape (Rect 2 3), Shape (Circle 1.5)]

> shapes
[Shape (Rect 2 3), Shape (Circle 1.5)] :: [Shape]

> map area shapes
```

## Existential

开启 `ExistentialQuantification` 扩展后，可以用 `forall` 关键字来限定类型，实现类似于 GADT 的效果。

```haskell
data Shape = forall a. (HasArea a) => Shape a
```

引入 `Data.Constraint` 库后，还可以将 typeclasses 作为参数：

```haskell
-- 需要开启 GADTs, KindSignatures, ConstraintKinds
data Some :: (* -> Constraint) -> * where
  Some :: c a => a -> Some c

> :t [Some 5, Some True] :: [Some Show]
[Some 5, Some True] :: [Some Show] :: [Some Show]
```

# Varadic functions

用 typeclass 可以实现可变参数的函数：

```haskell
class Addition t where
  add :: Int -> t

instance Addition Int where
  add x = x

instance (Addition t) => Addition (Int -> t) where
  add i = \x -> add (x+i)
```

令 `Int` 和 `Int -> t` 都成为 `Addition` 的实例，那么 `Int -> Int -> t` 也是 `Addition` 的实例了（`Addition (Int -> t) => Addition (Int -> Int -> t)`）。依次类推，相当于 `Int -> ... Int` 都是 `Addition` 的实例，因此可以在后面使用任意多的函数。

```haskell
> add (5 ::Int) (4 :: Int) (3 :: Int) :: Int
12
```
