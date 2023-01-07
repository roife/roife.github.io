---
layout: "post"
title: "「PLFA」 07 Negation"
subtitle: "否定"
author: "roife"
date: 2023-01-07

tags: ["Agda@编程语言", "读书笔记@Tags", "Programming Language Foundations in Agda@读书笔记", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 否定

给定命题 `A`，当 `A` 不成立时，它的否定形式 `¬ A` 成立。否定可以用“蕴含假”来阐述：

```agda
infix 3 ¬_

¬_ : Set → Set
¬ A = A → ⊥
```

其中 `¬ A` 的证据为一个函数 `λ{ x → N }`，`N` 的类型为 `⊥`，表示“假设 `A` 成立，那么会产生矛盾”。这是**归谬法**（Reductio ad Absurdum）的一种形式：若从 `A` 可得出 `⊥`， 则 `¬ A` 成立。

如果 `A` 与 `¬ A ` 均成立，那么得到了矛盾，即 `⊥`。

```agda
¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x
```

## `A → ¬ ¬ A`

```agda
¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}
```

这个证明的含义如下：已知 `A` 成立，如果假设 `¬ A` 也成立，那么就会导出矛盾。

另一种等价写法是：

```agda
¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x
```

要证明的结论为 `¬ A` 时，可以将 `A` 作为参数。

## `¬ ¬ ¬ A → ¬ A`

```agda
¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)
-- 或者 ¬¬¬-elim ¬¬¬x x =  ¬¬¬x (¬¬-intro x)
```

## `(A → B) → (¬ B → ¬ A)`

```agda
contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)
```

这条定律也称为**换质换位律**（contraposition）。

# 不等性

## 定义

```agda
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)
```

不等性可以直接利用否定定义。

对于 `¬ A` 证明时可以用 absurd pattern `λ ()` 表示 `A : ⊥`。agda 会先化简到 normal form 然后判断是否有证据证明等式成立（有没有 constructor 能用于这种情况）：

```agda
_ : 1 ≢ 2
_ = λ()
```

#ir `⊥ → ⊥`

```agda
id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()
```

可以证明上面两个证明等价：

```agda
id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())
```

此处需要证明 `∀ x → id ≡ id′`，但是由于 `x : ⊥`，没有 constructor，因此其相等性是 trivial 的。

可以证明任意两个否定的证明都是等价的：

```agda
assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))
```

# 一些否定相关的命题

## `¬ (n < n)`

```agda
<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s n<n) = <-irreflexive n<n
```

## Trichotomy

```agda
suc-≡ : ∀ {m n : ℕ}
  → suc m ≡ suc n
    -------------
  → m ≡ n
suc-≡ sucm≡sucn = cong (λ x → x ∸ 1) sucm≡sucn

data Tri (m n : ℕ) : Set  where

  forward :
      (m < n) × ¬ (m ≡ n) × ¬ (n < m)
      -------
    → Tri m n

  fixed :
      ¬ (m < n) × (m ≡ n) × ¬ (n < m)
      -------
    → Tri m n

  flipped :
      ¬ (m < n) × ¬ (m ≡ n) × (n < m)
      -------
    → Tri m n

trichotomy : ∀ (m n : ℕ) → Tri m n
trichotomy zero zero = fixed ((λ ()) , refl , (λ ()))
trichotomy zero (suc n) = forward (z<s , (λ ()) , (λ ()))
trichotomy (suc m) zero = flipped ((λ ()) , (λ ()) , z<s)
trichotomy (suc m) (suc n) with trichotomy m n
... | forward (m<n , ¬m≡n , ¬n<m) = forward (s<s m<n , (λ x → ¬m≡n (suc-≡ x)) , λ{ (s<s n<m) → ¬n<m n<m })
... | flipped (¬m<n , ¬m≡n , n<m) = flipped ((λ{ (s<s m<n) → ¬m<n m<n }) , (λ x → ¬m≡n (suc-≡ x)) , s<s n<m)
... | fixed (¬m<n , m≡n , ¬n<m) = fixed ((λ{ (s<s m<n) → ¬m<n m<n }) , cong suc m≡n  , λ{ (s<s n<m) → ¬n<m n<m })
```

## `⊎-dual-×`

```agda
⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = →-distrib-⊎

¬⊎-implies-¬× : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
¬⊎-implies-¬× = λ{ (inj₁ ¬a) → λ x → ¬a (proj₁ x) ; (inj₂ ¬b) → λ x → ¬b (proj₂ x) }
```

# 排中律是“无可辩驳”的

排中律（Law of the Excluded Middle）的形式如下：

```agda
postulate
  em : ∀ {A : Set} → A ⊎ ¬ A
```

在直觉逻辑中不能证明排中律，但是能证明排中律的否定的否定成立，即排中律无可辩驳（irrefutable）：

```agda
em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ a → k (inj₁ a)))
-- k : ¬ (A ⊎ ¬ A)
```

为了构造 `¬ ¬ (A ⊎ ¬ A)`，需要利用 `¬ (A ⊎ ¬ A)` 构造 `⊥`，即构造 `A ⊎ ¬ A` 然后应用。

考虑构造它的右边 `¬ A`，需要利用 `A` 构造 `⊥`。恰好 `¬ (A ⊎ ¬ A)` 的左边可以实现这一步。

下面五条定律等价，任意一条定律蕴含其它定律：
- 排中律：∀ (A : Set) → A ⊎ ¬ A
- 双重否定消去：∀ (A : Set) → ¬ ¬ A → A。
- 皮尔士定律：∀ (A B : Set) → ((A → B) → A) → A。
- 蕴涵表示为析取：∀ (A B : Set) → (A → B) → ¬ A ⊎ B。
- 德摩根定律：∀ (A B : Set) → ¬ (¬ A × ¬ B) → A ⊎ B。

# `Stable`

```agda
Stable : Set → Set
Stable A = ¬ ¬ A → A

neg-stable : ∀ {A : Set} → Stable (¬ A)
neg-stable = λ ¬¬¬a a → (¬¬¬-elim ¬¬¬a) a

×-stable : ∀ {A B : Set}
  → Stable A
  → Stable B
    --------------
  → Stable (A × B)
×-stable sa sb =
  λ ¬¬a×b → sa (λ ¬a → ¬¬a×b (λ a×b → ¬a (proj₁ a×b))) ,
            sb (λ ¬b → ¬¬a×b (λ a×b → ¬b (proj₂ a×b)))
```
