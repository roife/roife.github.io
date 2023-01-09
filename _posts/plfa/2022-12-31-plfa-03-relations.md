---
layout: "post"
title: "「PLFA」 03 Relations"
subtitle: "关系"
author: "roife"
date: 2022-12-31

tags: ["Agda@编程语言", "读书笔记@Tags", "Programming Language Foundations in Agda@读书笔记", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---


# 小于等于关系

```agda
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤_
```

此处的 `-------` 并不是语法，而是注释行，特地写成 inference rules 的形式。

从依赖函数的角度，constructor `s≤s` 可以看成将命题 `m ≤ n` 转换成 `suc m ≤ suc n`。

此外，这里 `_<_` 的优先级为 4，低于算术运算的优先级，而且结合方式为 `infix`，因此像 `1 < 2 < 3` 这样的定义是不合法的。

## Indexed datatype

在 `_≤_` 的定义中，`z≤n` 和 `s≤s` 是 constructor，`zero ≤ n`、`m ≤ n` 和 `suc m ≤ suc n` 是具体的类型。

其中，`m n : ℕ` 是 indices，分别对应着 `_≤_` 的左边和右边。Indices 在类型中出现时，类型的签名为 `x → Set` 的形式，表示这个类型需要加上参数。

注意，类型中的 indices 和 constructor 中参数的并不对应，例如 `z≤n` 只有一个参数，但是这个类型有两个 indices，这是因为其中一个 indices 在定义中提供了（即左边的 `zero`）。但是一般会让二者顺序相同。

## Implicit arguments

Constructor 中 `∀ {n : ℕ}` 使用了花括号，表示 implicit arguments。在检查时 agda 编译器会从后面的命题中自动推导此处填入的参数。

这些参数也可以显式给出：

```agda
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))
```

```agda
-- 即使加上了名字，m 和 n 的声明顺序也不能颠倒
_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))
```

```agda
-- 选择性声明
_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)
```

除了隐式参数外，也可以用 `_` 来让 agda 显式推导一个项：

```agda
+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _
```

如果推导失败，agda 会报错。

## Inversion

`s≤s` 可以从小 `m ≤ n` 得到大 `suc m ≤ suc n`，然而这一关系倒过来也是成立的。

对于 `∀ {m n : ℕ}`，从 `m ≤ n → suc m ≤ suc n` 是一个单射，因此这一关系的逆命题也成立，即 invert 原来的规则：

```agda
inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n
```

```agda
inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl
```

# 序关系的性质

## 自反性

```agda
≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl
-- ≤-refl {suc n} = s≤s (≤-refl {n})
```

## 传递性

```agda
≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)
```

这里的归纳方式与前面有区别。前面是在某一个变量（`n`）上进行归纳，这里是对 evidence `m≤n` 进行归纳。

这里没有 `≤-trans (s≤s m≤n) z≤n` 之类的情况，因为这些情况是不可能出现的。

## 反对称性

```agda
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)
```

此处需要注意的是 base case，由 `≤-antisym z≤n z≤n` 知 `n ≡ m ≡ zero`，即证明 `zero ≡ zero`，由等式的自反性成立。

Inductive case 则利用了等式的 congruence。

## 完全性

Agda 中的所有函数都必须是 total 的，但是关系（用 datatype 定义）可以不是。

首先定义 totality（析取）：

```agda
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n
```

### Parameterized datatype

这里的 `m` 和 `n` 与之前的 indices 定义有所不同，它们被定义为了 parameters。这也可以写成 indices 的形式：

```agda
data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n
```

类型里的每个 parameter 都转换成构造子的一个 implicit argument，并且用了全称量词。

从类型签名中可以发现，使用 parameters 时，类型签名为 `Set`；使用 indices 时，类型签名为 `ℕ → ℕ → Set`。

### Totality 的证明

证明 `_≤_` 的 totality 需要用 `with` 语句讨论两种情况。

```agda
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)
```

### `with` 语句

`with` 语句可以用于模式匹配。`with` 关键字的后面跟一个表达式以及多行 cases，每行以省略号（`...`）和一个竖线（`|`）开头，并且需要缩进。

### 辅助函数

上面的 `with` 语句也可以用一个辅助函数来进行模式匹配：

```agda
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)
```

## 单调性

`≤` 满足单调性，即：

```agda
∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q
```

这个证明可以被拆成三段：

```
m ≤ n, p ≤ q
⇒ m + p ≤ n + p, n + p ≤ n + q
⇒ m + p ≤ n + q
```

```agda
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)
```

# 严格不等关系

```agda
infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n
```

严格不等关系与不等关系最重要的区别为“0 小于任何数的后继，而不小于 0”。

严格不等关系不是自反的，但是满足 Trichotomy：对于任意的 `m` 和 `n`，`m < n`、`m ≡ n` 或者 `m > n` 三者有且仅有一者成立。

## 传递性

```agda
<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    ---------------
  → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)
```

## `m < n iff suc m ≤ n`

```agda
≤-iff-< : ∀ {m n : ℕ}
        → suc m ≤ n
        ---------------
        → m < n
≤-iff-< {zero} (s≤s sm≤n) = z<s
≤-iff-< {suc m} (s≤s sm≤n) = s<s (≤-iff-< sm≤n)

<-iff-≤ : ∀ {m n : ℕ}
        → m < n
        ---------------
        → suc m ≤ n
<-iff-≤ {zero} z<s = s≤s z≤n
<-iff-≤ {suc m} (s<s m≤n) = s≤s (<-iff-≤ m≤n)
```

# 奇偶性

奇偶性是一个一元关系，因此也称为谓词（predicate）。

```agda
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```

此处的 `suc` 是重载的 constructor。到目前为止，包括 `ℕ` 中定义的 `suc`，总共已经有三种定义。Agda 不允许重载已定义的名字， 但是允许重载 constructor。

并且 `even` 和 `odd` 是互相递归定义的，在定义之前需要先声明标识符。

## 两数之和为偶数

```agda
e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)
```

此处的证明也是互相定义的，因此同样先给出各自的类型声明，然后给出具体的定义（证明）。

同理可以证明奇数相加为奇数：

```agda
e+o≡o : ∀ {m n : ℕ}
      → even m
      → odd  n
      ---------------
      → odd (m + n)
e+o≡o {m} {n} em on rewrite (+-comm m n) = o+e≡o on em

o+o≡e : ∀ {m n : ℕ}
      → odd m
      → odd n
      ---------------
      → even (m + n)
o+o≡e (suc em') on = suc (e+o≡o em' on)
```

# Canonical Binary

## 定义

之前定义的 `Bin` 允许存在前导零，因此一个数字会有多种 `Bin` 的表示方式。

现在定义 canonical form `Can`。一个二进制字符串是标准的，当且仅当它开头是 1 （表示一个正数）， 或者它仅是一个 0 （表示 0）。

定义谓词 `One : Bin → Set`，仅当参数的开头为 1 时合法。那么非零 `Can`，要求对应的 `Bin` 必须满足 `One`。

```agda
data One : Bin → Set where

  I' :
    -------------
    One (⟨⟩ I)

  suc-I' : ∀ {n : Bin}
          → One n
          ------------
          → One (n I)

  suc-O' : ∀ {n : Bin}
         → One n
         ------------
         → One (n O)

data Can : Bin → Set where

  zero :
       ---------------
       Can (⟨⟩ O)

  from-one : ∀ {n : Bin}
           → One n
           ---------------
           → Can n
```

然后要定义 `Can` 上的加法，可以分两种情况。0 的情况是 trivial 的，非零的情况则按照二进制加法的规则进行计算：遇到 1 则将其变 0，直到遇到一个 0 将其变 1。

```agda
inc-keeps-one : ∀ {x : Bin}
              → One x
              ---------------
              → One (inc x)

inc-keeps-one I' = suc-O' I'
inc-keeps-one (suc-I' onex) = suc-O' (inc-keeps-one onex)
inc-keeps-one (suc-O' onex) = suc-I' onex

inc-keeps : ∀ {x : Bin}
  → Can x
    -----------
  → Can (inc x)

inc-keeps zero = from-one I'
inc-keeps (from-one onex) = from-one (inc-keeps-one onex)
```

接着可以重新定义将自然数转换成 `Can` 的函数：

```agda
to-can : ∀ {n : ℕ}
         ----------
         → Can (to n)

to-can {zero} = zero
to-can {suc n} = inc-keeps (to-can {n})
```

## `_+-Bin_`

接下来，为了证明 `to-from` 命题，需要先定义 `Bin` 上的加法，并证明一些引理：

```agda
_+-Bin_ : Bin → Bin → Bin
⟨⟩ +-Bin b = b
a  +-Bin ⟨⟩ = a
(a O) +-Bin (b O) = (a +-Bin b) O
(a O) +-Bin (b I) = (a +-Bin b) I
(a I) +-Bin (b O) = (a +-Bin b) I
(a I) +-Bin (b I) = (inc (a +-Bin b)) O

+-Bin-zeroˡ : ∀ {m : Bin}
  → Can m
    --------------------
  → (⟨⟩ O) +-Bin m ≡ m
+-Bin-zeroˡ zero = refl
+-Bin-zeroˡ (from-one I') = refl
+-Bin-zeroˡ (from-one (suc-I' x)) = refl
+-Bin-zeroˡ (from-one (suc-O' x)) = refl

+-Bin-incˡ : ∀ {m n : Bin}
  → (inc m) +-Bin n ≡ inc (m +-Bin n)
+-Bin-incˡ {⟨⟩} {⟨⟩} = refl
+-Bin-incˡ {⟨⟩} {n O} = refl
+-Bin-incˡ {⟨⟩} {n I} = refl
+-Bin-incˡ {m O} {⟨⟩} = refl
+-Bin-incˡ {m O} {n O} = refl
+-Bin-incˡ {m O} {n I} = refl
+-Bin-incˡ {m I} {⟨⟩} = refl
+-Bin-incˡ {m I} {n O} rewrite +-Bin-incˡ {m} {n} = refl
+-Bin-incˡ {m I} {n I} rewrite +-Bin-incˡ {m} {n} = refl

+-Bin-homo : ∀ (a b : ℕ)
  → to (a + b) ≡ (to a) +-Bin (to b)
+-Bin-homo zero b rewrite +-Bin-zeroˡ (to-can {b}) = refl
+-Bin-homo (suc a) b rewrite +-Bin-incˡ {to a} {to b}
                                    | +-Bin-homo a b = refl

+-Bin-double : ∀ (m : Bin)
  → One m
    ----------------
  → m +-Bin m ≡ m O
+-Bin-double (⟨⟩ I) I' = refl
+-Bin-double (m I) (suc-I' onem) rewrite (+-Bin-double m onem) = refl
+-Bin-double (m O) (suc-O' onem) rewrite (+-Bin-double m onem) = refl

+-Bin-zeroʳ : ∀ {m : Bin}
  → Can m
    --------------------
  → m +-Bin (⟨⟩) ≡ m
+-Bin-zeroʳ zero = refl
+-Bin-zeroʳ (from-one I') = refl
+-Bin-zeroʳ {m I} (from-one (suc-I' onem)) = refl
+-Bin-zeroʳ {m O} (from-one (suc-O' x)) = refl
```

## `to-from`

然后证明 `One` 是满足 `to-from` 的：

```agda
to-from-one : ∀ (x : Bin)
  → One x
    ---------------
  → to (from x) ≡ x

to-from-one _ I' = refl
to-from-one (x I) (suc-I' onex) rewrite +-identityʳ (from x)
                                | +-Bin-homo (from x + from x) 1
                                | +-Bin-homo (from x) (from x)
                                | to-from-one x onex
                                | +-Bin-double x onex
                                | +-Bin-zeroʳ {x} (from-one onex)
                                = refl

to-from-one (x O) (suc-O' onex) rewrite +-identityʳ (from x)
                                    | +-Bin-homo (from x) (from x)
                                    | to-from-one x onex
                                    | +-Bin-double x onex = refl
```

最后得到 `to-from`

```agda
to-from : ∀ (x : Bin)
  → Can x
    ---------------
  → to (from x) ≡ x

to-from _ zero = refl
to-from x (from-one onex) = to-from-one x onex
```
