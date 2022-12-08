---
layout: "post"
title: "「Haskell 学习」 03 Higher order function"
subtitle: "高阶函数，foldl 与 foldr"
author: "roife"
date: 2022-11-11

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# `foldr` 与 `foldl`

## `foldr`

```haskell
foldr :: Foldable t => (a -> b -> b) -> b -> t a -> b
foldr f v [] = v
foldr f v (x:xs) = f x (foldr xs)
```

`foldr ⊕ e [x1, x2, x3, ..., xn]` 等价于 `x1 ⊕ (x2 ⊕ (x3 ... (xn ⊕ e)...)`。

`map` 也可以用 `foldr` 定义：

```haskell
map' :: (a -> b) -> [a] -> [b]
map' f = foldr (\l ls -> f l : ls) []
```

## `foldl`

```haskell
foldl :: (a -> b -> a) -> a -> [b] -> a
foldl f v [] = v
foldl f v (x:xs) = foldl f (f v x) xs
```

可以看出，`foldl` 是尾递归的形式。但是由于惰性求值，这个过程实际上并不能节省内存。因此 `foldl` 还有一个惰性求值的版本 `Data.List.foldl'`。

`foldl ⊕ e [x1, x2, x3 ... xn]` 等价于 `(.. ((e ⊕ x1) ⊕ x2)..) ⊕ xn`。

## `foldl1` 与 `foldr1`

如果列表保证至少有一个元素，则可以不用提供单位元。

```haskell
foldr1 :: (a -> a -> a) -> [a] -> a
foldr1 _ [x] = x
foldr1 f (x:xs) = f x (foldr1 f xs)
foldr1 _ _ = error "foldr1 empty list"
```

```haskell
foldl1 :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs) = foldl f x xs
foldl1 _ [] = error "foldl1 empty list"
```

同样，也有惰性求值定义的 `foldl1'` 和 `foldr1'`。

## 在无穷列表上 `fold`

`foldl` 和 `foldr` 在无穷列表上 `fold` 时行为并不一致。其中 `foldl` 会无法停机，而 `foldr` 可以正常停机。

```haskell
> let f = repeat False
> foldr (&&) True f
False
> foldl (&&) True f -- 不会停止
```

这个问题的根源在于 Haskell 是惰性求值的。如果 `foldr` 作用在一个无穷列表中，并且某一次调用 `f` 没有对第二个参数求值，那么对列表剩余部分的求值就会终止。

`foldr` 计算的计算过程如下（后面的 `foldr` 是 lazy 的）：
- `foldr (&&) True [False, ...]`
- `True && (foldr (&&) False [False, ...])`
- `True && False && (foldr (&&) False [False, ...])`
- `False && (foldr (&&) False [False, ...])` 构建列表时直接短路了
- `False`

而 `foldl` 的计算过程如下：
- `foldl (&&) True [False, ...]`
- `foldl (&&) (True && False) [False, ...]`
- `foldl (&&) ((True && False) && False) [False, ...]` 一直构建这个列表

所以 `foldl` 会先尝试构造整个表达式，解决方法是用 `foldr` 代替 `foldl`。

这里就算用 `foldl'` 也不行，因为 `foldl'` 变成了下面的情况：
- `foldl' (&&) True [False, ...]`
- `foldl' (&&) (True && False) [False, False, ...]`
- `foldl' (&&) False [False, ...]`
- `foldl' (&&) (False && False) [False, ...]` 一直死循环

# `mapAccumL` 与 `mapAccumR`

这两个函数可以在求值时记录每个值的求值结果：

```haskell
mapAccumL :: (acc -> x -> (acc, y)) -> acc -> [x] -> (acc, [y])
mapAccumL _ s [] = (s, [])
mapAccumL f s (x:xs) = (s'', y : ys) where
    (s', y) = f s x
    (s'', ys) = mapAccumL f s' xs
```

```haskell
> mapAccumL (\sum -> \a -> (sum + a,even (sum + a))) 0 [1, 3, 4, 5, 6]
(19, [False, True, True, False, False])
```

```haskell
mapAccumR :: (acc -> x -> (acc, y)) -> acc -> [x] -> (acc, [y])
mapAccumR _ s [] = (s, [])
mapAccumR f s (x:xs) = (s'', y : ys) where
    (s'', y) = f s' x
    (s', ys) = mapAccumR f s xs
```

# 复合函数

用 `(.)` 可以复合两个函数，及 `h(x) = f(g(x))`。

```haskell
(.) :: (b -> c) -> (a -> b) -> (a -> c)
(.) f g = \x -> f (g x)
```

需要注意区分 `.` 和 `$`。前者会传入两个函数得到一个新函数（按**左结合**计算）；后者则是按 `$` 分割计算，并按照**右结合**进行计算。

类似可以定义一个“链式”操作：

```haskell
(|>) :: b -> (b -> c) -> c
(|>) = flip ($)
> 4 |> div 8 |> even |> not
```

这个运算符在 `Data.Function` 定义为 `(&)`。
