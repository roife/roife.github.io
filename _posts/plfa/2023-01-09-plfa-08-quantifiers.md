---
layout: "post"
title: "「PLFA」 08 Quantifiers"
subtitle: "全称量化与存在量化"
author: "roife"
date: 2023-01-09

tags: ["Agda@编程语言", "读书笔记@Tags", "Programming Language Foundations in Agda@读书笔记", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 全称量化

## 定义

我们用**依赖函数类型**（Dependent Function Type）来表示全称量化（Universals）。

给定一个变量 `x : A` 和一个带有自由变量 `x` 的命题 `B x`。如果对于所有 `M : A`，命题 `B M` 都成立，那么全称量化命题 `∀ (x : A) → B x` 成立。变量 `x` 在 `B x` 中是自由的，但是在 `∀ (x : A) → B x` 中是约束的。

`∀ (x : A) → B x` 成立的证明是一个依赖函数 `λ (x : A) → N x`。其中 `N x : B x`，且 `N x` 和 `B x` 都包含了自由变量 `x : A`。可以理解为 `∀ (x : A) → B x` 的证明是一个**函数**，可以将 `M : A` 转换成 `B M` 成立的证明：

```agda
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M
```

## 全称量词与函数

类似于 `→-elim`，`∀-elim` 对应了依赖函数应用。

普通函数是依赖函数的一种特殊形式。在普通函数中，值域与定义域无关。作为蕴含的证明时，普通函数的参数和结果都是证明的一部分。而依赖函数作为全称量词的证明时，它的值域会随着参数而改变，且参数是类型的一个元素，结果依赖于参数。

## Dependent products

依赖函数类型也被称为 Dependent Product：假设类型 `A` 有 `n` 个成员，分别为 `x₁ x₂ ⋯ xₙ`。其中，对于每个 `xᵢ`，类型 `B xᵢ` 有 `mᵢ` 个成员（即有 `mᵢ` 中情况），那么类型 `∀ (x : A) → B x` 有 `m₁ * ⋯ * mₙ` 个成员。因此 `∀ (x : A) → B x` 也可以记作 `Π[ x ∈ A ] (B x)`。

事实上，`∀` 与特定类型的 `×` 有着同构关系，`∀` 可以写成 `×` 一样的形式：`∀ (x : A) → B x ≃ ⟨ B x₁ , B x₂ , ⋯ B xₙ ⟩`。设 `B xᵢ` 有 `mᵢ` 中情况，那么共有 `Π mᵢ` 种可能。

```agda
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

-- extensionality doesn't satisfy this
postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → (∀ x → f x ≡ g x)
      -----------------
    → f ≡ g

∀-× : ∀ {B : Tri → Set}
  → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× {B} =
  record
    { to = λ f → ( (f aa) , (f bb) , (f cc) )
    ; from = λ{ (a , b , c) → λ{ aa → a ; bb → b ; cc → c } }
    ; from∘to = λ f → ∀-extensionality λ{ aa → refl ; bb → refl ; cc → refl }
    ; to∘from = λ{ (a , b , c) → refl }
    }
```

但是 dependent product 这个名字并不准确（在后面的“存在量化”一章中能看到这一点，因为存在量词有时也被称为 dependent products），因此通常不使用这个名字。

## 分配律

全称量词对于合取分配：

```agda
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to   = λ A→B×C → ( (λ a → proj₁ (A→B×C a)) , (λ a → proj₂ (A→B×C a)) )
    ; from = λ A→B×A→C a → ( (proj₁ A→B×A→C) a , (proj₂ A→B×A→C) a )
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }
```

全称命题的析取蕴涵了析取，但是反过来不成立：

```agda
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ x) = λ a → inj₁ (x a)
⊎∀-implies-∀⊎ (inj₂ y) = λ a → inj₂ (y a)
```

# 存在量化

## 定义

给定一个变量 `x : A` 和一个带有自由变量 `x` 的命题 `B x`。如果存在 `M : A` 使得命题 `M B` 成立，那么称存在量化（Existentials）的命题 `Σ[ x ∈ A ] B x`成立。变量 `x` 在 `B x` 中是自由的，但是在 `Σ[ x ∈ A ] B x` 中是约束的。

存在量化的命题通常用下面的结构表示：

```agda
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
```

## Syntax declaration

为了方便书写，可以使用 syntax declaration 来简化：

```agda
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
```

这里定义了用 `Σ-syntax` 表示 `Σ`，并声明可以用 `Σ[ x ∈ A ] B` 来书写。这里定义 `Σ-syntax` 的好处在于，只有导入了 `Σ-syntax` 后才能使用这种 syntax declaration。

## 存在量词与积

`Σ[ x ∈ A ] B x` 成立的证明由 `⟨ M , N ⟩` 组成，其中 `M : A`，`N : B M`。因此可以用 `record` 类型来等价定义：

```agda
record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′
```

存在量化的证明也是一个积，但是它的第二个分量依赖于第一个分量，通常被称为 Dependent Pair。前面遇到的类型积的第二个分量不取决于第一个分量中的变量，这种积是 dependent pair 的一种特殊形式。

当 product 作为合取的证明时，它的两个分量都是证明的一部分。而 dependent pair 作为存在量词的证明时，它的第一个分量是数据类型的一部分，且第二个分量是依赖于第一个分量的证明。

此外，存在量化的证明有时也被称为 Dependent Product，这就和前面的全称量化混淆了。因此通常不这么称呼。（实际上我觉得将存在量化的证明称为“依赖积”更加合适，这样恰好能和“依赖函数”相对应）

## Dependent sums

存在量化也被称为 dependent sums：假设类型 `A` 有 `n` 个成员，分别为 `x₁ x₂ ⋯ xₙ`。其中，对于每个 `xᵢ`，类型 `B xᵢ` 有 `mᵢ` 个成员（即有 `mᵢ` 中情况），那么类型 `Σ [ x ∈ A] B x` 有 `m₁ + ⋯ + mₙ` 个成员。这也是为什么使用 `Σ` 来表示存在量化。

```agda
data Tri′: Set where
  aa : Tri′
  bb : Tri′
  cc : Tri′

∃-⊎ : ∀ {B : Tri′ → Set}
  → (∃[ x ] B x) ≃ (B aa ⊎ B bb ⊎ B cc)
∃-⊎ =
  record
    { to = λ{ ⟨ aa , y ⟩ → inj₁ y ; ⟨ bb , y ⟩ → inj₂ (inj₁ y) ; ⟨ cc , y ⟩ → inj₂ (inj₂ y) }
    ; from = λ { (inj₁ x) → ⟨ aa , x ⟩ ; (inj₂ (inj₁ x)) → ⟨ bb , x ⟩ ; (inj₂ (inj₂ x)) → ⟨ cc , x ⟩ }
    ; from∘to = λ{ ⟨ aa , y ⟩ → refl ; ⟨ bb , y ⟩ → refl ; ⟨ cc , y ⟩ → refl }
    ; to∘from = λ { (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ x)) → refl }
    }
```

## Agda 标准库中的定义

```agda
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → Bx) = ∃[ x ] Bx
```

Agda 中使用了隐式参数来定义 `∃`，`Σ` 是 `∃` 的证明。

并且这里还使用了上面说的 syntax declaration，这样只有在引入 `∃-syntax` 后才能用这种特殊的语法。

## `∃-elim`

`∃` 可以提供全称命题中要求的条件。

```agda
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y
```

## Currying 的推广

如果改变一下 inferece rules 推导线的位置，上面这个证明可以看成：

```agda
∃-elim′ : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
    ---------------
  → ∃[ x ] B x
  → C
∃-elim′ f ⟨ x , y ⟩ = f x y
```

实际上 `∀ x → B x → C` 和 `∃[ x ] B x → C` 是同构的。由于全称量化的证明是 dependent function，存在量化的证明是 dependent pair，因此这个同构关系可以看作是**推广的 currying**：

```agda
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
```

## 分配律

存在量化的分配律和全称量化对偶。

```agda
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to   = λ { ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩ ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩ }
    ; from = λ { (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩ ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , inj₂ Cx ⟩ }
    ; from∘to = λ { ⟨ x , inj₁ Bx ⟩ → refl ; ⟨ x , inj₂ Cx ⟩ → refl }
    ; to∘from = λ{ (inj₁ ⟨ x , Bx ⟩) → refl ; (inj₂ ⟨ x , Cx ⟩) → refl }
    }
```

```agda
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ( Bx , Cx ) ⟩ = ( ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ )
```

## `odd & even`

前面用后继定义了 `odd` 和 `even`，但是用 `∃` 定义更符合直觉：

```agda
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

-- o : odd n
-- odd-∃ o : ∃[ m ] (1 + m * 2 ≡ n)
-- Goal: ∃[ m ] ( m * 2 ≡ suc n ≡⟨ n ≡ 1 + m * 2 ⟩ suc (suc (m * 2)) )

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩
```

同样，还需要进行反方向的证明：

```agda
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)
```

# 存在量化、全称量化和否定

`¬ ∃` 与 `∀ → ¬` 同构。考虑到 `∃` 是 `⊎` 的推广，`∀` 是 `×` 的推广，这一点非常自然（`¬ (a ⊎ b) ≡ ¬ a × ¬ b`）。

```agda
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }
```

此外，`∃¬` 蕴含 `¬∀`，但是反过来不成立（因为 `A` 可能为空）：

```agda
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ = λ x→Bx → ¬Bx (x→Bx x)
```

# `ℕ ≃ ∃[ b ](Can b)`

## `≡-homomorphism`

首先定义性质：`a ≡ b → B a ≡ B b`。

```agda
≡-homomorphism : ∀ {A : Set}
  → (A → Set)
  → Set
≡-homomorphism {A} B =
  ∀ {x : A}
  → (bx : B x)
  → (by : B x)
    ----------
  → bx ≡ by
```

然后证明它对于 `One` 和 `Can` 都成立：

```agda
One-≡-homo : ≡-homomorphism One
One-≡-homo I' I' = refl
One-≡-homo (suc-I' x) (suc-I' y) = cong suc-I' (One-≡-homo x y)
One-≡-homo (suc-O' x) (suc-O' y) = cong suc-O' (One-≡-homo x y)

Can-≡-homo : ≡-homomorphism Can
Can-≡-homo zero zero = refl
Can-≡-homo zero (from-one (suc-O' ()))
Can-≡-homo (from-one (suc-O' ())) zero
Can-≡-homo (from-one x) (from-one y) = cong from-one (One-≡-homo x y)
```

## `Σ-≡`

```agda
Σ-≡ : ∀ {A : Set} {B : A → Set} {a c : A}
  → ≡-homomorphism B
  → a ≡ c
  → (b : B a)
  → (d : B c)
    ---------------------
  → ⟨ a , b ⟩ ≡ ⟨ c , d ⟩
Σ-≡ ≡-homo a≡c ba bc rewrite a≡c | ≡-homo ba bc = refl
```

## `Bin-isomorphism`

```agda
Bin-isomorphism : ℕ ≃ ∃[ x ](Can x)
Bin-isomorphism =
  record
    { to = λ{ n → ⟨ to n , to-can {n} ⟩ }
    ; from = λ{ ⟨ x , y ⟩ → from x }
    ; from∘to = from-to
    ; to∘from = λ{ ⟨ x , y ⟩ → Σ-≡ Can-≡-homo (to-from x y) (to-can {from x}) y}
    }
```
