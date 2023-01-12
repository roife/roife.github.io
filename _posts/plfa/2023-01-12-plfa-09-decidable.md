---
layout: "post"
title: "「PLFA」 09 Decidable"
subtitle: "证明与计算"
author: "roife"
date: 2023-01-12

tags: ["Agda@编程语言", "读书笔记@Tags", "Programming Language Foundations in Agda@读书笔记", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 证明与计算

## `Bool`

在讨论计算前，需要先定义 `Bool` 类型来表示 `⊤` 和 `⊥`。

```agda
data Bool : Set where
  true  : Bool
  false : Bool
```

## `≤` 与 `≤ᵇ`

首先定义“小于等于”在证明和计算两种形式下的运算符。

其中 `z≤n` 对应 `zero ≤ᵇ n`，`s≤s` 对应 `suc m ≤ᵇ suc n`；而 `suc m ≤ᵇ zero` 对应的是 `⊥`，因此无需给出 constructor。

```agda
-- _≤_
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
```

```agda
-- _≤ᵇ_
infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n
```

## 从两种角度判断命题

对于相关的命题，也可以从证明和计算两种观点下进行判定：

```agda
2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))
```

```agda
_ : (2 ≤ᵇ 4) ≡ true
_ =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎
```

## 证明与计算的桥梁

上面用证明与计算两种方式殊途同归地判定了“小于等于”相关的命题。不难发现二者是有联系的：判断为真的命题可证明，判断为假的命题无法构造证明。

下面来建立二者的联系：

```agda
T : Bool → Set
T true   =  ⊤
T false  =  ⊥
```

`T` 把计算结果映射到了类型：如果值为真，那么对应的类型可以构造（命题可证明）；否则，对应的类型无法构造（无法证明）。

`T b` 当且仅当 `b ≡ true` 成立时成立，因此可以利用 `T` 在类型中描述计算的结果为 `true` 还是 `false`。

```agda
T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt   =  refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl  =  tt
```

下面证明 `≤ᵇ` 与 `≤` 的等价性：

```agda
≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero    n       tt  =  z≤n
≤ᵇ→≤ (suc m) zero    ()
≤ᵇ→≤ (suc m) (suc n) t   =  s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n        =  tt
≤→≤ᵇ (s≤s m≤n)  =  ≤→≤ᵇ m≤n
```

虽然证明和计算有着对应关系，但是在证明时，可以不用考虑不成立的情况（agda 可以自动排除为空的类型），因此写起来更方便；而计算的优势在于可以让计算机自动进行计算。

下面我们尝试结合二者的有点，构造一个可以自动计算的证明。关键点在于怎么表述“命题为真，并给出证明”，以及“命题为假，并给出假命题判断的过程”。

# Decidable

```agda
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A
```

正如布尔值，这个类型有两个 constructor，其中一个仅当命题为真时成立，另一个仅当命题为假时成立。

有了两个 constructor 后，就可以用类型实现“计算”了：用递归可以模拟归纳的过程，如果递归得到了真命题的 constructor，说明可以用其配合递归过程构建出真命题的证明，返回 `yes`；反之，如果得到了假命题的 constructor，说明命题为假，返回 `no`。

最好避免直接使用 `Bool`，需要的时候使用 `Dec`。

## `_≤?_`

以 `≤?` 为例，其真命题的 constructor 为 `z≤s` 与 `s≤s`，下面构建其假命题的 constructor：

```agda
¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n
```

可以看出假命题的 constructor 和真命题是一一对应的。下面构建 `_≤?_`：

```agda
_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? n                   =  yes z≤n
suc m ≤? zero                =  no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n  =  yes (s≤s m≤n)
...               | no ¬m≤n  =  no (¬s≤s ¬m≤n)
```

`_≤?_` 的构建过程和计算类似，但是它的计算过程返回的是一个 `Dec A`。对于命题 `P`，每次返回 `yes Q` 时表明命题 `P` 为真，且其证明为 `Q`；对于 `no R` 则类似。

`_<?_` 自身就蕴含了证明，而不需要像 `≤ᵇ` 一样通过证明 `≤ᵇ→≤` 和 `≤→≤ᵇ` 来证明其正确性。

## 从 `_≤ᵇ_` 到 `_≤?_`

在定义 `_≤?_` 的过程中可以复用 `_≤ᵇ_`：

```agda
_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p
```

当命题为真时，使用 `≤ᵇ→≤` 来构建证明，此时 agda 推断出第三个参数 `T (m ≤ᵇ n)` 是 `⊤`，并构建证明；当命题为假时，agda 会取一个 `m ≤ n` 的证明（`λ ()`），得到 `⊥`，然后取反。

## 将 `Dec` 转换为 `Bool`

`Dec` 转换成 `Bool` 的过程称为 **Erasure**。

```agda
⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false
```

使用 erasure，很容易就可以从 `_≤?_` 中得到 `_≤ᵇ_`。

如果 `D : Dec A`，那么 `T ⌊ D ⌋` 成立当且仅当 `A` 成立。

```agda
toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x
```

这样就可以轻松地得到：`T (m ≤ᵇ′ n)` 成立当且仅当 `m ≤ n` 成立。

```agda
≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness
```

# 逻辑连接符

## `_∧_`

```agda
infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false
```

在 Emacs 中，第三个等式等号的左边显示为灰色，表示等式的顺序会影响等式的结果。（在这个例子中没有影响）

同样为 `Dec` 也可以定义与运算，即使用 product。

```agda
infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }
```

## `_∨_`

```agda
infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false
```

```agda
infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }
```

## `not`

```agda
not : Bool → Bool
not true  = false
not false = true
```

```agda
¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x)  =  no (¬¬-intro x)
¬? (no ¬x)  =  yes ¬x
```

注意 `¬?` 并没有改变命题的真假性：
- 对于 `yes x` 来说，它将 `A` 成立转换成了 `¬ ¬ A` 不成立
- 对于 `no ¬x` 来说，它将 `A` 不成立转换成了 `¬ A` 成立

## `_⊃_`

`_⊃_` 与蕴含 `→` 对应：

```agda
_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false
```

```agda
_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))
```

## `_iff_`

```agda
_iff_ : Bool → Bool → Bool
true iff true = true
true iff false = false
false iff true = false
false iff false = true
```

```agda
_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes x ⇔-dec yes y = yes (record { to = λ _ → y ; from = λ _ → x })
yes x ⇔-dec no y = no (λ z → y (_⇔_.to z x))
no x ⇔-dec yes y = no (λ z → x (_⇔_.from z y))
no x ⇔-dec no y = yes (record { to = λ a → ⊥-elim (x a) ; from = λ b → ⊥-elim (y b) })
```

# Proof by Reflection

Proof by Reflection 运用了上面的 `Dec`，通过计算让编译器按照规则自动推导出证明。

例如对于一种特殊的减法，要求第一个数字大于等于第二个数字：

```agda
minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m
```

在使用这个减法时，调用方不得不提供 `n≤m` 的证明：

```agda
_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl
```

在上面的证明中，`n` 和 `m` 都是确定的数字，并且 `_≤?_` 已经写出了 `_≤_` 证明的构建规则，因此不妨让编译器自动推导证明：

```agda
_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)
```

此处将证明定义为隐式参数，就可以留给编译器自动推导了：
- 如果 `n ≤ m` 成立，`⌊ n ≤? m ⌋` 为 `true`，隐式参数的类型规约为 `⊤`；此处 agda 会接收这个证明（隐式参数）
- 否则，类型规约为 `⊥`，agda 无法提供对应的值，报错

这样就可以直接使用减法而不提供证明了：

```agda
_ : 5 - 3 ≡ 2
_ = refl
```

这种惯用语法非常普遍，标准库定义了 `True` 表示 `T ⌊ ? ⌋`：

```agda
True : ∀ {Q} → Dec Q → Set
True Q = T ⌊ Q ⌋
```
