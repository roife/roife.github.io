---
layout: "post"
title: "「PLFA」 02 Induction"
subtitle: "归纳证明"
author: "roife"
date: 2022-12-30

tags: ["Agda@编程语言", "读书笔记@Tags", "Programming Language Foundations in Agda@读书笔记", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 加法结合律

```agda
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎
```

此处的 `≡⟨ cong suc (+-assoc m n p) ⟩` 中放的是推导的依据。`(+-assoc m n p)` 表示 `(m + n) + p ≡ m + (n + p)`，`cong succ _` 表示在 `_` 的两端应用这个 constructor。应用了这个依据后，等式的左边应该和已有的条件相同，并得到等式的右边。

若某个关系在应用了给定的函数后仍然保持不变，则称该关系满足**合同性**（Congruence）。 若 `e` 是 `x ≡ y` 的证据，则 `cong f e` 是 `f x ≡ f y` 的证据。

# 全称量词

`∀` 是全称量词。全称量词对应的 evidence（证明）是一个函数，可以理解为“全称量词要求传入任意一个值都能使命题成立，即证明传入任意一个参数仍然成立”。

```agda
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

-- 也可以写成

+-assoc : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → (m + n) + p ≡ m + (n + p)
```

这个函数的结果类型“依赖于”参数（与参数有关），因此称为 dependent function。

# 加法交换律

首先证明两个 lemmas：

```agda
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎
```

```agda
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎
```

然后就可以很自然地得到加法交换律：

```agda
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎
```

# 重排定理

```agda
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q
  ∎
```

此处 `sym` 表示交换等式两边。

# `rewrite`

`rewrite _` 后面跟一个等式 `_`。当前命题中出现的“等式 `_` 的左边”都会被改写成“等式 `_` 的右边”。

## 证明加法结合律

```agda
+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl
```

## 证明加法交换律

```agda
+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl
```

此处最后一个证明用了 `|` 分隔两次 `rewrite`，表示二者依此进行。

## 证明乘法分配律

```agda
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite (*-distrib-+ m n p) | (+-assoc p (m * p) (n * p)) = refl
```

## 证明乘法结合律

```agda
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite (*-distrib-+ n (m * n) p) | sym (*-assoc m n p) = refl
```

## 证明乘法交换律

```agda
*-zero : ∀ (n : ℕ) → zero * n ≡ n * zero
*-zero zero = refl
*-zero (suc n) rewrite sym (*-zero n) = refl

*-distrib-+′ : ∀ (n m : ℕ) → n * (suc m) ≡ n * m + n
*-distrib-+′ zero m = refl
*-distrib-+′ (suc n) m rewrite (*-distrib-+′ n m) | (+-suc′ (m + n * m) n) | (+-assoc m (n * m) n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite sym (*-zero n)= refl
*-comm (suc m) n rewrite (*-distrib-+′ n m) | (+-comm n (m * n)) | (*-comm m n) = refl
```

## 证明减法-加法结合律

```agda
∸-zero : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-zero zero = refl
∸-zero (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite (∸-zero n) | (∸-zero (n + p)) | (∸-zero p) = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite (∸-+-assoc m n p) = refl
```
