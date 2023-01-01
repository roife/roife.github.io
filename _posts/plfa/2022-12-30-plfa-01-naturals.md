---
layout: "post"
title: "「PLFA」 01 Naturals"
subtitle: "自然数和归纳类型"
author: "roife"
date: 2022-12-30

tags: ["Agda@编程语言", "读书笔记@Tags", "Programming Language Foundations in Agda@读书笔记", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Agda 的一些语法

## 编译指令

类似 Haskell，用 `{-# #-}` 给出。

其中 `{-# BUILTIN NATURAL ℕ #-}` 表示用数字 `2` 代替 `suc (suc zero)`。这里会使用 haskell 的任意精度整数进行计算。

类似的还有运算符相关：

```agda
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}
```

## 导入模块

用 `import x as y` 可以将模块导入当前作用域，用 `open y using z` 可以将模块中的名称添加到当前作用域，用 `renaming (a to b; c to d)` 可以进行重命名。

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
```

运算符中的 `_` 表示项，例如此处 `begin_` 的 `begin` 是前缀运算符，`_≡_` 是中缀运算符。

当然 `import` 和 `open` 也可以放在一起：

```agda
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
```

## 优先级

类似 haskell：

```agda
infixl 6  _+_  _∸_
infixl 7  _*_
```

## 柯里化

类似的，agda 也支持柯里化。`ℕ → ℕ → ℕ` 表示 `ℕ → (ℕ → ℕ)`。

## hole

用 `?` 可以表示一个 hole，让 agda 来补全。

## totality

在传统的静态类型语言中，用户无需使用编译器就能写代码。然后，编译器在不运行代码的情况下进行检查。

在 DT 中，如果编译器想要检查一个证明 `f 1 = 0`，那么 type checker 就必须对 `f` 进行求值。因此为了保证停机，定理证明器都要求是所有的函数是 total 的。

# 自然数

## 定义

自然数可以归纳定义

```agda
data ℕ : Set where
  zero : ℕ          -- base case
  suc  : ℕ → ℕ      -- inductive case
```

`data` 表示这是一个归纳定义（inductive definition），即用 constructors 来定义类型。

此处 `ℕ : Set` 表示 `ℕ` 是一个类型（agda 中用 `set` 表示类型）。

## 加法

自然数的运算是一个递归函数。

例如加法的定义：

```agda
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)
```

此处 `m + n` 也可以写作 `_+_ m n`。因此后面的两行实际上是函数的模式匹配。

在这个定义中，较大数字的定义基于较小数字，而且有一个极小元 `zero`，因此称为 **well-founded**。

## `≡`

Agda 中，用 `=` 表示定义，用 `≡` 表示相等。

```agda
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎
```

这里的 `_` 表示不绑定具体名称。

此处的推导过程包括两部分：类型签名，并绑定该类型对应的项。项为类型提供了证据（evidence），并由一串等式（`≡`）组成。这串等式由 `begin` 开头，由 `∎`（可以读作“qed”）结尾，中间用 `≡⟨⟩` 表示等价推导，用来分隔。

当然这里也可以直接用 `refl` 来让 agda 自己来推导。（对于二元关系 `xRy` 如果满足 `xRx`，那么 `R` 是自反的，即 reflexive）。

## 乘法与阶乘

```agda
_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)
```

``agda
_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ (suc m) = n * (n ^ m)
```

## Monos（减法）

这里只考虑自然数的减法，不考虑出现负数的情况。

```agda
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n
```

如果模式匹配中有情况没有覆盖到，那么 agda 会报告错误。

注意此处的第二条规则为 `zero ∸ suc n  =  zero`，如果写成 `zero ∸ n = zero`，那么对于 `zero ∸ zero` 就有两条规则可以应用。一般来说不推荐这样，可以使用编译选项 `{-# OPTIONS --exact-split #-}` 让 agda 报错。

# 二进制表示

```agda
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- 1011 = ⟨⟩ I O I I
```

由于存在前导零，因此表示可能不唯一。

下面定义几个相关的函数：

```agda
inc : Bin → Bin
inc (n I) = (inc n) O
inc (n O) = n I
inc ⟨⟩  = ⟨⟩ I

from : Bin → ℕ
from ⟨⟩    = 0
from (n I) = 2 * (from n) + 1
from (n O) = 2 * (from n)

to : ℕ → Bin
to 0       = ⟨⟩ O
to (suc n) = inc (to n)
```
