---
layout: "post"
title: "「PLFA」 04 Equality"
subtitle: "等价性"
author: "roife"
date: 2023-01-01

tags: ["Agda@编程语言", "读书笔记@Tags", "Programming Language Foundations in Agda@读书笔记", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Equality

## 定义

```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_
```

`refl` 给出了自反性的证明。

`_≡_` 的第一个参数由 `x : A` 给出，第二个参数由 `A → Set` 给出。当然这里也能将其定义为 `A → A → Set`。即 `refl` 的定义为：

```agda
refl : ∀(x : A) → x ≡ x
```

这里的 `x` 对应了 `_≡_` 的左边，可以是任意类型，因此定义为 parameter；第二个参数对应了 `_≡_` 的右边，必须用 index，这是因为如果用 parameter 定义（不妨设为 `(y : A)`），那么 `refl` 的定义就会变成：`refl : ∀(x y : A) → x ≡ y`。这样不能表达“相等”的含义。

前面在讨论 `_≤_` 的时候也证明了自反性，但是对于 `_≡_` 来说，`refl` 是构建这个类型的**唯一** constructor，而对于 `_≤_` 来说，自反性只是在特殊情况下（两个参数相同）的性质。

## `≡` 是等价关系

相等是一个等价关系，而一个等价关系是自反、对称和传递的。自反性在相等的定义中已经有了，因此下面需要证明对称性和传递性。

### 对称性

```agda
sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl
```

下面解释一下 `sym refl = refl` 这个证明：
- 左边的 `refl` 类型为 `x ≡ y`，而 `_≡_` 的定义中只有 `refl` 这一个 constructor，因此必然是 `refl`
- 在 `refl` 中，对应的 `y` 的类型与 `x` 相同，**因此 agda 认为在这种情况下 `x` 与 `y` 相同**
- 此处右边的类型 `y ≡ x` 变成 `x ≡ x`，即可以通过 `refl` 构造

第二步很重要，后面都是利用这个进行化简的。

`sym` 不只是对于等价性的证明，同时也是颠倒等号两边的函数。

### 传递性

```agda
trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl  =  refl
```

同上。

### 合同性

合同性（Congruence）的含义为**如果两个项相等，那么对它们使用相同的函数，其结果仍然相等**。

```agda
cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl  =  refl
```

两个参数的函数也满足合同性：

```agda
cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl  =  refl
```

在函数上的等价性也满足合同性（如果两个函数是相等的，那么对于每个输入，相同的输入会得到相同的输出）：

```agda
cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl
```

### 替换性

替换性（Substitution）的含义为**如果两个值相等，其中一个满足某谓词，那么另一个也满足此谓词**。

```agda
subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px
```

注意和合同性的区别，这里也可以写成：

```
subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
  → P x
    ---------
  → P y
```

# 等式串

## 定义

```agda
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning
```

`begin_` 是装饰性的，因此它直接返回了传入的参数本身。`_∎` 提供了自反的等式，即 `x ∎ = x ≡ x`。

`_≡⟨⟩_` 和 `_≡⟨_⟩_` 是右结合的。

`_≡⟨⟩_` 的两边是相同项的等价变形（例如根据定义来化简项，agda 会将两边都化到最简，然后检查是否相同），可以看成是 `_≡⟨refl⟩_`。

`_≡⟨_⟩_` 可以**用传递性转换项**，本质上是一个 `trans`。

因此整个等式链都可以用 `trans` 来构建。

## 以 `trans` 为例

以 `trans` 的证明为例：

```agda
trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎
```

等价于 `begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))`。

其中，`z ∎` 的类型为 `z≡z`，因此 `y ≡⟨ y≡z ⟩ (z ∎)` 的类型为 `(trans y≡z z≡z)`，同理整个式子的类型为：

```agda
trans x≡y (trans y≡z refl)
-- trans x≡y (trans y≡z z≡z)
```

由于等式链证明都是 `begin_`，`_∎` 结尾，因此整个等式链可以转换为 `trans ... (trans ... (trans e refl))`。

## 模块

这里使用了 `module...where` 来定义模块，一个模块可以有隐式或显式的参数，并且使用缩进来区分模块。

使用 `open` 能够将模块内的名字导入到当前的环境中。

## 假设

使用 `postulate` 可以引入一个假设，而无需证明。但是错误的假设会导出错误的结论。

```agda
postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
```

# `rewrite`

## 定义

给定 `P(m + n)` 的证据，如果有相等等式 `m + n ≡ n + m`，那么 `P(n + m)` 也应当成立。这一机制便是 `rewrite`。在 agda 中，可以用编译指令告诉编译器哪个类型对应了这种“等价性”。

```agda
{-# BUILTIN EQUALITY _≡_ #-}
```

如果要进行多次 `rewrite`，则应该用 `|` 分隔。

## `rewrite` 的本质

`rewrite` 实际上是 `with` 的应用：

```agda
even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev  rewrite +-comm n m  =  ev

-- 等价于

even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev
```

`with` 可以对多个表达式一起进行模式匹配，需要匹配的表达式之间用 `|` 分隔。

多个模式进行匹配时，位于后面的表达式的**类型**会泛化前面的项的**值**：假设位于前面的项 `e1 : t1` 匹配 `p1`，那么后面的项 `e2 : t2` 的类型 `t2` 中包含 `e1` 的部分会被替换成 `p1`。因此多个表达式匹配时的顺序是至关重要的。

例如上面需要对 `m + n` 和 `+-comm m n` 进行匹配。这里首先用到了 dot pattern `.(n + m)` 匹配 `m + n`。因此 `+-comm m n` 的类型 `m + n ≡ n + m` 被泛化为 `n + m ≡ n + m`，与 `refl` 匹配。

同时，`ev` 中的 `m + n` 也被替换为 `n + m`，恰好就是要证明的条件（即要 `rewrite` 的条件），可以直接作为结果。

### dot pattern

Dot pattern 由一个 `.` 与一个表达式组成。此处的 `_+_` 不是一个 constructor，也不能 invert，因此直接不能用于模式匹配。

但是 `n` 和 `m` 却可以从这个 case 下其它的 pattern 中推导出来，此时可以用 dot pattern 来表示这个 patten，而不直接对其进行匹配。从其它 pattern 中推导出结果后，再代入到 dot pattern 中进行 unify。

在上面的例子里，首先进行替换，然后将泛化后的 `+-comm m n` 与 `refl` 匹配，得到 `+-comm` 两边的 `m + n` 与 `n + m` 是等价的（`refl` 的类型），因此前面的 dot pattern 能够 unify。

如果上面的例子里不用 `refl`，而是用其它的证据，那么无法推断出 `m + n` 可以和 `n + m` unify。

### 用 `subst` 进行 `rewrite`

实际上，`rewrite` 也可以用 `subst` 来实现：

```agda
even-comm″ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm″ m n emn =  subst even (+-comm m n) emn
```

# Leibniz equality

## 定义

上面用的 equality 的形式来自于 Martin-Löf，于 1975 年发表。而 Leibniz 于 1686 年也发布过一个关于 equality 的形式。Leibniz 认为相等性不可分辨的实体（Identity of Indiscernibles）：“两个对象相等当且仅当它们满足完全相同的性质。”这条原理被称作莱布尼兹定律（Leibniz’ Law），与 Spock’s Law 相关：“一个不造成区别的区别不是区别。”

下面会定义 Leibniz equality，并证明它于 Martin-Löf equality 的等价性（两个项是 Leibniz equal iff. 它们是 Martin-Löf equal 的）。

Leibniz equality 的定义如下：当每个对于 `x` 成立的性质 `P` 对于 `y` 也成立时，`x ≐ y`。这个定义隐含了一个反向的条件，即“每个对于 `y` 成立的性质 `P` 对于 `x` 也成立”。

```agda
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y
```

这里为了能够写出命题 `∀ (P : A → Set)`，必须显式写出类型 `A`，因而在定义的左边不能写 `x≐y`，而要写 `_≐_ {A} x y`。

Leibniz equality 是前面 substitution theorem 的逆命题。

## levels

同时，这里还使用了**levels**。由罗素悖论，`Set` 的类型不能为 `Set`，因此需要定义一个更高的 level：`Set : Set₁`，`Set₁ : Set₂`。其中 `Set` 等价于 `Set₀`。

由于 `_≐_` 定义的右边出现了 `Set`，因此 `_≐_` 的类型不能再是 `Set`，而应该是 `Set₁`。

## 性质

Leibniz equality 是自反和传递。其中自反性来自于恒等函数，传递性来自于函数组合。

```agda
refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px  =  Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px  =  y≐z P (x≐y P Px)
```

对称性则比较复杂。对称性要求证明 `∀ P`，`P x → P y`，那么 `P y → P x`。

```agda
sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx
```

首先需要构造一个能得到 `P x` 成立的谓词。取谓词 `Q z`，当 `P z` 成立时，`P x` 也成立。那么 `Q x` 显然成立，等价于 `_≐_` 的自反性。

然后将 `Q` 和 `Q x` 应用于 `x≐y`。由 `x≐y` 知 `Q y` 成立，因此 `P y → P x`。

这个证明的核心在于谓词 `Q z = P z → P x` 的构造。利用自反性使得 `Q x` 成立；`_≐_` 的定义使得 `Q y` 成立。

# 更高 level 下的 equality

全面给出了 `Set₀` 下的 equality 的定义，下面考虑在更高 level 下的 equality。

## Universe Polymorphism

为此需要引入 universe polymorphism：一个定义可以根据任何等级 `ℓ` 来做出。首先需要导入 level 相关的部分：

```agda
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
-- 为了防止混淆将引入的 zero 和 suc 进行重命名
```

level 的定义和 ℕ 同构（如果不进行重命名的话，constructor 也相同）：

```agda
lzero : Level
lsuc  : Level → Level

Set₀ = Set lzero
Set₁ = Set (lsuc lzero)
Set₂ = Set (lsuc (lsuc lzero))
```

此外还有一个运算符用于返回两个 level 中较大的那一个：

```agda
_⊔_ : Level → Level → Level
```

## 定义

```agda
data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x
```

使用 `Set (lsuc ℓ)` 可以表示 `Set ℓ` 的下一个层级。

标准库中的大部分函数都泛化到了任意层级，例如：

```agda
sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡′ y
    ------
  → y ≡′ x
sym′ refl′ = refl′


_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y


_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)
```
