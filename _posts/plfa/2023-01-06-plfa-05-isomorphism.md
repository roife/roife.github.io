---
layout: "post"
title: "「PLFA」 05 Isomorphism"
subtitle: "同构与嵌入"
author: "roife"
date: 2023-01-06

tags: ["Agda@编程语言", "读书笔记@Tags", "Programming Language Foundations in Agda@读书笔记", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# λ 表达式

```agda
λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ }

-- 等价于定义了一个函数 `f`
f P₁ = N₁
...
f Pₙ = Nₙ
```

如果只有一个模式且模式是一个变量，那么可以用 `λ x → N` 或者 `λ (x : A) → N`。

# 函数组合

```agda
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

-- 也可以定义成 g ∘ f  =  λ x → g (f x)
```

# 外延性

函数的外延性（Extensionality）定义了判断函数相等的规则：

Agda 没有预设外延性成立，但我们可以假设其成立。它与 agda 的理论是一致的：

```agda
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

更一般的，外延性可以扩展到依赖函数：

```agda
postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

## 两种加法的等价性

```agda
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)

same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))
```

# 同构

如果两个集合有一一对应的关系，那么它们是**同构的**（isomorphic）。

```agda
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
```

上面的定义中包含了同构的四个要素：
- 函数 `to : A → B` 与函数 `from : B → A`
- `from` 是 `to` 的左逆（left-inverse）的证明 `from∘to`
- `from` 是 `to` 的右逆（right-inverse）的证明 `to∘from`

即 `from∘to` 与 `to∘from` 都是恒等函数。

## `record`

`record` 类似于只有一个 constructor 的 `data`，具体的区别会在后面讨论。

上面的定义也等价于：

```agda
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g
```

从中可以看出，`record` 内的函数在使用时需要多传入一个对应的 `record` 类型的值。

可以用下面的语法构造 `record` 类型的值：

```agda
record
  { to    = f
  ; from  = g
  ; from∘to = g∘f
  ; to∘from = f∘g
  }

-- 等价于 mk-≃′ f g g∘f f∘g
```

## 同构是一个等价关系

### 自反性

```agda
≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }
```

根据 `from` 和 `to` 的定义，`from (to x) ≡ x` 且 `to (from x) ≡ x`，因此可以直接用 `refl` 证明。

### 对称性

```agda
≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym A≃B =
  record
    { to      = from A≃B
    ; from    = to   A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }
```

### 传递性

```agda
≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C =
  record
    { to       = to   B≃C ∘ to   A≃B
    ; from     = from A≃B ∘ from B≃C
    ; from∘to  = λ{x →
        begin
          (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎}
    ; to∘from = λ{y →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎}
     }
```

此处 `from∘to B≃C (to A≃B x)` 的类型为 `from B≃C (to B≃C (to A≃B x)) ≡ to A≃B x`。

## 使用同构进行相等论证

前面定义了 `≡` 的 `begin_`、`_≡⟨_⟩_` 以及 `_∎` 来进行相等性论证。类似的，同构关系也可以定义这样的论证语法。

```agda
module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning
```

# 嵌入

**嵌入（embedding）**是一种弱化的同构概念。同构要求证明两个类型内的值一一对应，而嵌入允许是一对多的关系（第一种类型包含在第二种类型中）。

```agda
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_
```

从定义中可以看出没有 `to∘from`，因为从 `B` 映射到 `A` 后，就丢失了 `B` 的信息。

## 嵌入的性质

### 自反性与传递性

嵌入是自反和传递的（证明方法和同构类似），但不是对称的。

```agda
≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎}
     }
```

### 互相嵌入的类型

如果两个类型相互嵌入，且其嵌入函数相互对应，那么它们是同构的。这是一种弱化的反对称性。

```agda
≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎}
    }
```

### 使用嵌入进行相等论证

```agda
module ≲-Reasoning where
  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning
```

# `⇔`

命题的等价于 `⇔` 的定义如下：

```agda
infix 0 _⇔_
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_
```

类似的，`⇔` 是自反、对称、传递的。

```agda
⇔-refl : ∀ {A : Set}
  --------
  → A ⇔ A
⇔-refl =
  record
    { to   = λ{x → x}
    ; from = λ{y → y}
    }

⇔-sym : ∀ {A B : Set}
  → A ⇔ B
  --------
  → B ⇔ A
⇔-sym A⇔B =
  record
    { to   = from A⇔B
    ; from = to A⇔B
    }

⇔-trans : ∀ {A B C : Set}
  → A ⇔ B
  → B ⇔ C
  --------
  → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
    { to   = to B⇔C ∘ to A⇔B
    ; from = from A⇔B ∘ from B⇔C
    }
```
