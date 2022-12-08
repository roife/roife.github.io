---
layout: "post"
title: "「Haskell 学习」 02 List comprehension"
subtitle: "List comprehension"
author: "roife"
date: 2022-11-11

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# List Comprehension

List comprehension 可以用来构造列表，其中用 `x <- xs` 来对元素赋值：

```haskell
-- {x^2 |x in {1..100}, x < 10}
[x^2|x <- [0..100], x < 10]

-- {(x, y) | x in {1..4}, y in {1..4}}
[(x,y) | x <- [1..4], y <- [1..4]]
```

还可以用 List comprehension 定义常用函数：
- `map' f xs = [f x | x <- xs]`
- `filter' f xs = [x | x <- xs, f x]`

## Parallel list comprehension

上面的 list comprehension 中，如果有多个变量，则会依次取遍每个变量。

打开 `ParallelListComp` 扩展可以一次同时取若干个变量：

```haskell
> [(x,y) | x <- [1, 2, 3] | y <- [4, 5, 6]]
[(1,4),(2,5),(3,6)]
```

当一个变量被取完时，剩下没有取遍的值就不会再继续取了，因此错误使用可能会导致结果变少：

```haskell
> [(x, y, z) | x <- [1, 2, 3] , y <- [4, 5, 6] | z <- [7, 8, 9]]
[(1, 4, 7), (1, 5, 8), (1, 6, 9)]

-- 取遍所有的 x, y
> [(x, y, z) | x <- [1, 2, 3] , y <- [4, 5, 6] | z <- cycle [7, 8, 9]]
[(1, 4, 7), (1, 5, 8), (1, 6, 9), (2, 4, 7), (2, 5, 8), (2, 6, 9), (3, 4, 7), (3, 5, 8), (3, 6, 9)]
```

## Generalised list comprehension

开启 `TransformListComp` 和 `ParallelListComp` 后，可以用类似 SQL 的语法操作列表：

```haskell
analysis = [(the product, sum cost) |
            (city, product, cost) <- table,
            then group by product using groupWith,
            then sortWith by (sum cost)]
```

# 一些应用

- 组合

```haskell
import Data.List (delete)

permutation :: Eq a => [a] -> [[a]]
permutation [] = [[]]
permutation xs = [y : ys | y <- xs, ys <- permutation (delete y xs)]
```

- 错位排列

```haskell
import Data.List (delete)

derangements :: [Int] -> [[Int]]
derangements [] = [[]]
derangements l = [x : xs | x <- l, xs <- derangements (delete x l), x /= length l]

derangements' n = map reverse (derangements [1 .. n])
```

- 组合

```haskell
import Data.List (tails)

combinations :: Int -> [a] -> [[a]]
combinations 0 _ = [[]]
combinations n xs = [y:ys | y:xs'<- tails xs, ys <- combinations (n-1) xs']
```

- 矩阵转置

```haskell
transpose :: [[a]] -> [[a]]
transpose [] = []
transpose ([]:xss) = transpose xss
transpose ((x:xs):xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [t | (_:t) <- xss])
```

- 矩阵乘法

```haskell
infixl 5 |*|

(|*|) :: Num a => [[a]] -> [[a]] -> [[a]]
(|*|) a b = [[ sum $ zipWith (*) ar bc | bc <- transpose b ] | ar <- a]
```
