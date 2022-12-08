---
layout: "post"
title: "「Haskell 学习」 01 Basics"
subtitle: "Types, Typeclasses, Expressions, Functions"
author: "roife"
date: 2022-11-11

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 常见类型

- `Bool`：包括 `True` 和 `False` 两个值，可以用 `&&`、`||`、`not` 进行运算
- `Char`：字符型，用单引号，如 `'a'`，也可以用 Unicode 字符
- 整数
  - `Int`：带符号整数，$-2^{31} \sim 2^{31} - 1$ 或 $-2^{63} \sim 2^{63} - 1$，取决于系统字长
  - `Word`：无符号整数，大小类似于 `Int`
  - `Integer`：任意精度整数
  - `Data.Int`/`Data.Word` 模块中还有 `Int8` 和 `Word8` 等类型
  - 字面量：`0o` 八进制；`0x` 十六进制
- 浮点数
  - `Float`/`Double`
  - 有理数类型 `Rational`：`0.5 == 1 % 2`
- 字符串 `String` 即 `[Char]`
- 元组类型 `(a, b)`，二元元组可以用 `fst` 和 `snd` 获取两个值
- 函数类型 `T1 -> T2`

## Curry-ing

用 `curry` 和 `uncurry` 可以转换柯里化函数和非柯里化函数。

```haskell
> :t curry
curry :: ((a, b) -> c) -> a -> b -> c

> :t uncurry
uncurry :: (a -> b -> c) -> (a, b) -> c
```

## Polymorphism

如果函数的某个参数可以是任何类型，可以用类型变量表示（小写字母开头），则称函数为多态函数（Polymorphic Functions）。例如 `fst :: (a, b) -> a`。

如果参数可以是任意类型，但是对于类型的 typeclasses 有要求，则称为 ad-hoc polymorphism。声明时把 typeclasses 限定写在 `=>` 的左侧，如 `add :: Num a => a -> a -> a`。

Haskell 允许对不同参数类型进行重载，但是不允许对参数数量进行重载（因为函数默认是柯里化的，可以看作只有一个参数）。

## 类型别名

用 `type` 关键字可以给类型起别名（**不是定义新类型**）：

```haskell
type RGB = (Int, Int, Int)
```

# Typeclasses

Typeclasses 有点类似于 Java 中的 `interface`，具有共同属性的类型属于同一个 typeclasses，类型也可以通过实现 typeclasses 中的函数来成为某个 typeclasses 的实现。

- `Eq`：定义 `==` 或 `/=`
- `Ord`：定义 `<=`，并且要求实现 `Eq`
- `Enum`：定义 `toEnum` 和 `fromEnum`
  + `toEnum :: Int -> a`
  + `fromEnum :: a -> Int`
  + 实现了 `Enum` 的类型可以用 `..` 来枚举一个范围，如 `[1..10]`
- `Bounded`：定义 `maxBound :: a` 与 `minBound :: a`
- `Show`：定义 `show` 或 `showPrec`
  + `show :: a -> String`
  + `showPrec :: Int -> a -> ShowS`

## `Num`

![Int Typeclasses](/img/in-post/post-haskell/integer-type-classes.png){:height="800px" width="800px"}

图上为 `Num` 相关 typeclasses 之间的实现关系。其中，`Num` 和 `Eq` 之间的虚线表示只有 `GHC <= 7.4` 时有这个关系，后来设计者发现这是个错误，于是删除了这个关系。

数字之间转换可以用 `fromX` 和 `toX` 函数，例如 `fromInteger`。

### 浮点数

这里比较意外的是 `Float` 和 `Double` 也是 `Enum`，这是因为 Haskell 可以自动推断出枚举的步长：

```haskell
> [1.0, 1.5 .. 3.0]
[1.0, 1.5, 2.0, 2.5, 3.0]
```

此外，Haskell 中还有 `Nan` 和 `Infinity`，后者可以用 `isInfinity :: ReadFloat a => a -> Bool` 来进行判断。`Nan` 类型在用 `min` 和 `max` 进行大小比较时会很诡异，所以推荐用 `minNum` 和 `maxNum` 替代。

### 精度

在 `Data.Fixed` 中还有一种固定精度的浮点类型：`Fixed E0`、`Fixed E3` 等。

此外，也可以用 `Data.Number.CReal` 进行高精度计算。

### 科学记数法

开启 `NumDecimals` 扩展，当科学记数法表示的数字为整数时，返回 `Num` 而不是 `Fractional`。

```haskell
> :t 1.643e5
1.643e5 :: Fractional a => a

> :set -XNumDecimals
> :t 3.14159e6
3.14159e6 :: Num a => a
```

# 函数

函数定义的语法如下：

```haskell
<name> :: <arg1_type> -> <arg2_type> -> ... -> <argn_type> -> <result_type>
<name> <arg1> <arg2> ... <argn> = <body>
```

也可以用 λ 表达式：`\<a1> -> \<a2> -> .. -> \<an> -> <body>`。

## 尾递归与惰性求值

```haskell
-- 尾递归求和函数
total' [] n = n
total' (x:xs) n = total' xs (n+x)

total xs = total' xs 0
```

由于 Haskell 是惰性求值的，中间值会在最后一刻才进行计算，因此上面这个尾递归函数并不能真正优化内存使用：

```
total [1,2,3] 0
= total' [2,3] (1 + 0)
= total' [3] (2+ (1 + 0))
= total' [] (3 + (2 + (1 + 0)))
= (3 + (2 +(1 + 0)))
= (3 + (2 + 1))
= (3 + 3)
= 6
```

可以用 bang pattern（需要开启 `BangPattern` 扩展）或 `$!` 对参数进行强制求值。

```haskell
total' [] n = n
total' (x:xs) n = total' xs $! (x + n)
-- total'(x:xs) !n = total' xs (x + n)
```

# 表达式

## Conditional

```haskell
if <condition> then <true_exp> else <false_exp>
```

## Case/Pattern Maching

Case 表达式可以用来做模式匹配。

```haskell
case <exp> off
  <pat1> -> <ans1>
  <pat2> -> <ans2>
  ...
  <patn> -> <ansn>
  _ -> <ans_wildcard>
```

注意这里需要缩进表示属于同一个表达式，最后一个 `_` 表示通配符。

在定义函数时，也可以直接在定义时进行模式匹配：

```haskell
month :: Int -> Integer
month 1 = 31
month 2 = 28
...
month 12 = 31
month _ = error "invalid month"
```

## Guarded

Guarded expression 用 `|` 将条件分开，相当于多重的 `if...then...else` 语句：

```haskell
abs n
  | n > 0 = n
  | otherwise = -n
```

需要注意的是，这里的 `abs n` 后面不用跟 `=`，但是条件满足时用 `=`。

# 运算符

用 `` ` `` 可以将函数当作运算符使用，如 ``5 `div` 2``。

## 优先级

|   | 左结合                        | 无结合                                              | 右结合                  |
|-|-|-|
| 9 | `!!`                          |                                                     | `.`                        |
| 8 |                               |                                                     | `^`, `^^`, `**`         |
| 7 | `*`, `/`, `div`, `mod`, `rem` |                                                     |                         |
| 6 | `+`, `-`                      |                                                     |                         |
| 5 |                               |                                                     | `:`, `++`               |
| 4 |                               | `==`, `/=`, `<`, `<=`, `>`, `>=`, `elem`, `notElem` |                         |
| 3 |                               |                                                     | `&&`                    |
| 2 |                               |                                                     | `||`            |
| 1 | `>>`, `>>=`                   |                                                     |                         |
| 0 |                               |                                                     | `$`, `$!`, `$!!`, `seq` |

函数调用（包括 constructor）的等级最高，可以认为是 10 级。

比较实用的：
- `[a] !! n` 从列表取出第 `n` 个元素
- `a : [a]` 用来连接元素和列表，`[a] ++ [a]` 用来连接两个列表

`$` 非常有用，可以将表达式分割成若干个过程，并进行右结合：

```haskell
($) :: (a -> b) -> a -> b
```

## 运算符定义

用 `infixr`、`infixl` 和 `infix` 分别可以表示右结合、左结合和无结合。

```haskell
infixr 5 <->

<-> :: Int -> Int -> Int
(<->) x y = x - y
```

# `module`

## `module` 定义

如果不加 `(public_list)`，则默认 `module` 内的函数和类型都是公开的。

```haskell
module <ModuleName> (<public_list>) where
-- definition
```

## `import`

使用 `module` 内的函数时，需要写出完整路径，如 `Data.List.permutations`。使用 `import Data.List` 后，就可以直接用 `permutations`。

`import` 有很多种写法：
- `import M (f)`：只导入 `M.f`
- `import M hiding (f)`：只隐藏 `M.f`
- `import qualified M as M1`：将 `M1` 作为 `M` 的别名

# 常用库和函数

- `id :: a -> a`
- `const :: a -> b -> a`
  + `const id :: a -> b -> b`
- `flip :: (a -> b -> c) -> b -> a -> c`
- `error :: String -> a`
- `undefined :: a`
  + `undefined = error "Prelude.undefined"`
- `max, min :: Ord a => a -> a -> a`

列表相关：
- `null :: Foldable t => t a -> Bool`
- `length :: Foldable t => t a -> Int`
- `(!!) :: [a] -> Int -> a`
- `reverse :: [a] -> [a]`
- `head, last :: [a] -> a`
- `init, tail :: [a] -> [a]`：去掉列表最后一个元素、去掉第一个元素
- `map :: (a -> b) -> [a] -> [b]`
- `filter :: (a -> Bool) -> [a] -> [a]`
- `take, drop :: Int -> [a] -> [a]`
- `span, break :: (a -> Bool) -> [a] -> ([a], [a])`：从左到右，遇到第一个满足（不满足）条件的元素时停下，将列表分为两部分
- `takeWhile, dropWhile :: (a -> Bool) -> [a] -> [a]`
- `splitAt :: Int -> [a] -> ([a], [a])`
- `repeat :: a -> [a]`：重复一个元素，得到一个无穷列表
  + `replicate :: Int -> a -> [a]`
- `any, all :: Folable t => (a -> Bool) -> t a -> Bool`
- `and, or :: Foldable t => t Bool -> Bool`
- `elem, notElem :: (Foldable t, Eq a) => a -> t a -> Bool`
- `iterate :: (a -> a) -> a -> [a]`：将前一次迭代结果用于下一次
- `until ::  (a -> Bool) -> (a -> a) -> a -> a`
- `zip :: [a] -> [b] -> [(a, b)]`
  + `unzip :: [(a, b)] -> ([a], [b])`
  + `zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]`
- `concat :: Foldable t => t [a] -> [a]`
- `concatMap :: Foldable t => (a -> [b]) -> t a -> [b]`（`flatMap`）

此外，在 `Data.List` 中还有更多有用的函数。

字符串相关：
- `show :: Show a => a -> String`
- `read :: Read a => String -> a`：读取字符串，如果结果可能为多种类型，则需要用 `::` 指定类型
- `lines, unlines :: String -> [String]`：用 `\n` 分割（用 `\n` 连接）
- `words, unwords :: String -> [String]`：用空格分割（用空格连接）
