---
layout: "post"
title: "「PLFA」 06 Connectives"
subtitle: "合取、析取与蕴涵"
author: "roife"
date: 2023-01-06

tags: ["Agda@编程语言", "读书笔记@Tags", "Programming Language Foundations in Agda@读书笔记", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 合取

## 定义

给定两个命题 `A` 和 `B`，其**合取**（Conjunction）`A × B` 成立当 `A` 成立和 `B` 成立。

```agda
infixr 2 _×_

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B
```

`A × B` 的证明由 `⟨ M , N ⟩` 提供，其中 `M` 是 `A` 的证明，`N` 是 `B` 的证明。

反过来，从 `A × B` 中可以得到 `A` 的证明或 `B` 的证明：

```agda
proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y
```

## 引入操作与消去操作

当 `⟨_,_⟩` 出现在等式左边时，一般当作 destructor 进行模式匹配；出现在右边时一般用作 **constructor**。`proj₁` 和 `proj₂` 也可以称为 **destructor**。

此外，也会将 `⟨_,_⟩` 称为**引入**（introduce）合取，记作 `×-I`，将 destructor 称为**消去**（eliminate）合取，记作 `×-E₁` 和 `×-E₂`。

对于 constructor（引入）来说，运算符会出现在结果中；而对于 destructor（消去）来说，运算符会出现在假设中。或者说引入规则描述了“运算符在什么情况下成立”/“怎么样定义运算符”；消去规则描述了“运算符成立时，可以得出什么样的结论”/“怎么使用运算符”。

## η-equality for ×

```agda
η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

-- 为了得到等式左边，必须拆成 ⟨ x , y ⟩
```

## 另一种定义

可以模仿上一章对于同构的定义，使用 `record` 类型：

```agda
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
```

这里的 `constructor` 关键字使得我们可以用 `⟨ M , N ⟩′` 来进行构造，而不用写 `record { proj₁′ = M ; proj₂′ = N }`。

使用 `record` 引入 `constructor` 后就不用证明 η-equality 了，agda 默认 η-equality 成立（因为 `record` 只能有一个 constructor）。

```agda
η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl
```

事实上，这也是标准库中的定义。

## 类型的积

`A × B` 称为 `A` 与 `B` 的**积**（product），对应了 `record` 类型。在集合论中也称作笛卡尔积（Cartesian Product）。 如果 `A` 有 `m` 个不同成员，`B` 有 `n` 个不同成员， 那么类型 `A × B` 有 `m * n` 个不同成员。

## 交换律和结合律

积在在同构意义下满足交换律和结合率。

```agda
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }
```

```agda
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }
```

## `⇔ ≃ ×`

```agda
⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ A⇔B → ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B ⟩
    ; from = λ AB×BA → record { to = proj₁ AB×BA ; from = proj₂ AB×BA }
    ; from∘to = λ x → refl
    ; to∘from = λ y → η-× y
    }
```

# 真值

## 定义

```agda
data ⊤ : Set where

  tt :
    --
    ⊤
```

恒真有引入规则，但没有消去规则。

## η-equality for ⊤

```agda
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl
```

此处的模式匹配也是必要的，这样可以让 agda 确定 `w` 只有一个 constructor。

## 另一种定义

```agda
record ⊤′ : Set where
  constructor tt′
```

同理，这种定义下不需要模式匹配。

```agda
η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl
```

## 单元类型

`⊤` 称为**单元类型**（Unit Type），对应数字 1。

`⊤` **在同构意义下**是积类型的幺元。

```agda
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎
```

# 析取

## 定义

给定命题 `A` 和 `B`，**析取**（Disjunction） `A ⊎ B` 在 `A` 或 `B` 成立时成立。

```agda
-- 析取的优先级低于合取
infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B
```

`A ⊎ B` 的证明由 `inj₁ M`（`M` 是 `A` 的证明）或 `inj₂ N`（`N` 是 `B` 的证明）提供，记为 `⊎-I₁` 和 `⊎-I₂`。`inj₁` 和 `inj₂` 既能作为 constructor 使用，也能作为 destructor 使用。

对于析取式，通常用 `case-⊎` 消去，记为 `⊎-E`。

```agda
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y
```

## η-equality

对析取式先 destruct 然后用相同的 constructor，会得到原来的值：

```agda
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl
```

更普遍的，可以对析取直接应用一个函数：

```agda
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl
```

## 类型的和

给定两个类型 `A` 和 `B`，`A ⊎ B` 称为 `A` 与 `B` 的**和**，对应 `variant record` 类型
。在集合论中它也被称作**不相交并集**（Disjoint Union）。

如果 `A` 有 `m` 个不同成员，`B` 有 `n` 个不同成员， 那么 `A ⊎ B` 有 `m + n` 个不同成员。

## 交换律与结合律

```agda
⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to      = λ { A⊎B → case-⊎ inj₂ inj₁ A⊎B }
    ; from    = λ { B⊎A → case-⊎ inj₂ inj₁ B⊎A }
    ; from∘to = λ { (inj₁ x) → refl ; (inj₂ y) → refl }
    ; to∘from = λ { (inj₁ x) → refl ; (inj₂ y) → refl }
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to      = λ { A⊎B⊎C →
                      case-⊎ (λ A⊎B → case-⊎ inj₁ (inj₂ ∘ inj₁) A⊎B)
                             (inj₂ ∘ inj₂)
                             A⊎B⊎C}
    ; from    = λ { A⊎B⊎C →
                      case-⊎ (inj₁ ∘ inj₁)
                             (λ B⊎C → case-⊎ (inj₁ ∘ inj₂) inj₂ B⊎C)
                             A⊎B⊎C}
    ; from∘to = λ { (inj₁ (inj₁ a)) → refl
                  ; (inj₁ (inj₂ b)) → refl
                  ; (inj₂ c) → refl }
    ; to∘from = λ { (inj₁ a) → refl
                  ; (inj₂ (inj₁ b)) → refl
                  ; (inj₂ (inj₂ c)) → refl }
    }
```

# 假值

## 定义

恒假 `⊥` 从不成立，因此无法给出它成立的证明：

```agda
data ⊥ : Set where
  -- 没有语句
```

`⊥` 与 `⊤` 对偶。恒假没有引入规则，但是有消去规则：如果恒假成立，那么可以推出任何结论。

```agda

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()
```

这里是用了 **absurd pattern** `()`，表示不可能匹配任何值。

`uniq-η` 断言了 `⊥-elim` 和任何输入为 `⊥` 的函数等价：

```agda
uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()
```

## 空类型

`⊥` 是**空**（Empty）类型。由 absurd pattern 可知，没有值内匹配 `⊥` 类型。

在同构意义下，空是和类型的幺元。

```agda
⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ { (inj₂ a) → a }
    ; from = λ { a → (inj₂ a) }
    ; from∘to = λ { (inj₂ b) → refl }
    ; to∘from = λ { b → refl }
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
    { to = λ { (inj₁ a) → a }
    ; from = λ { a → (inj₁ a) }
    ; from∘to = λ { (inj₁ a) → refl }
    ; to∘from = λ { a → refl }
    }
```

由于空类型没有 constructor，因此上面在模式匹配时都不用考虑 `⊥` 的情况。

# 蕴含

给定 `A` 和 `B`，其蕴涵 `A → B` 成立，当且仅当在任何 `A` 成立的时候 `B` 也成立。

`A → B` 成立的证据为 `λ (x : A) → N`，其中 `N` 的类型为 `B`。给定蕴含 `A → B` 的证明 `L`，以及 `A` 的证明 `M`，那么 `L M ≡ N` 就是 `B` 的证明。即 `A → B` 的证明是一个函数，将 `A` 的证明转换成 `B` 的证明：

```agda
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M
```

`→-elim` 也叫 modus ponens，与函数应用相对应。

定义一个函数可以称为引入一个函数，使用一个函数称为消去一个函数。

## η-equality

引入后接着消去，得到的还是原来的值：

```agda
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl
```

## 函数类型

给定 `A` 和 `B`，`A → B` 称为从 `A` 到 `B` 的**函数空间**，也称为以 `B` 为底，`A` 为次数的幂。

如果类型 `A` 有 `m` 个不同成员， 类型 `B` 有 `n` 个不同成员，那么类型 `A → B` 有 `nᵐ` 个不同成员。

## 柯里化

类似于幂性质 `(p ^ n) ^ m  ≡  p ^ (n * m)`，函数类型有以下性质（柯里化，currying）：`A → (B → C)  ≃  (A × B) → C`。

其证明如下：

```agda
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
```

在 agda 中，函数默认是柯里化的。

类似上面的类比，其它的幂相关的运算定律在函数中也有对应的性质：

```agda
-- p ^ (n + m) = (p ^ n) * (p ^ m)
-- (A ⊎ B) → C  ≃  (A → C) × (B → C)
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

-- (p * n) ^ m = (p ^ m) * (n ^ m)
-- A → B × C  ≃  (A → B) × (A → C)
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }
```

# 分配律

在同构意义下，上面的类型满足类似代数运算的分配律。

## 积对于和分配

```agda
×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }
```

这条性质对应了逻辑学上的公式 `A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)`。

## 和对于积嵌入

```agda
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 -- 也可以定义为 ⟨ _ ,   inj₂ z′ ⟩ → (inj₂ z′)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }
```

上面的 `from` 函数有两种定义方式，但是当出现两个 `C` 时，不管哪一种都必须丢掉 `inj₂ z` 或 `inj₂ z′` 其中之一，因此和对于积只能嵌入，而不能同构。

## 弱分配律

```agda
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× A⊎B×C = case-⊎
                   inj₁
                   (λ B → inj₂ ⟨ B , (proj₂ A⊎B×C) ⟩)
                   (proj₁ A⊎B×C)
```
