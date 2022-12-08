---
layout: "post"
title: "「The Little Typer」 15 Imagine that..."
subtitle: "谬模式与排中律"
author: "roife"
date: 2021-04-09

tags: ["The Little Typer@读书笔记", "读书笔记@Tags", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "Pie@编程语言", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 谬模式

一个 statement 如果是 true 的，那么它会有对应的 evidence；反之，假命题则没有 evidence，这和 `Absurd` 有点像。

> **Principle of Explosion** / **ex falso quodlibet**
>
> If a false statement were true, then we might as well say anything at all.
>
> **注解**：即假命题可以推出其他任何命题。亦如 `ind-Absurd` 可以推导出任何类型

## `Absurd`

如果要表达一个假命题，或表达 `Not X`，可以借助 `Absurd`：

```lisp
(→ X
  Absurd)
; If there were a proof for X, then there would be a proof for Absurd
```

假设现在要证明一个命题为假。如提供一个假命题 `(= Nat 39 17)`，传入一个函数 `(→ (= Nat 39 17) Absurd)`，应该得到一个 `Absurd`。然而由于无法构建一个 `Absurd` 的值，所以也无法构建一个函数返回 `Absurd`，此时不能使用 λ 函数来实现这个类型，而需要另辟蹊径（如 `=consequence`）：因为无法构建一个 `Absurd` 的值，但是可以考虑写一个函数，对于假命题返回 `Absurd` 类型本身，对于真命题返回其他类型。

# `=consequence`

`=consequence` 可以传入两个 Nat 构建一个新的类型，可以理解为：“如果两个 Nat 相等，那么可以得到什么信息”。

- 对于 `(= 0 0)`，直接返回 `Trivial`（显然）
- 对于 `(= 0 (add1 j-1))` 或者 `(= (add1 n-1) 0)`，返回 `Absurd`（不可能）
- 对于 `(= (add1 n-1) (add1 j-1))`，则返回 `(= Nat n-1 j-1)`（新的信息）

|              | `0`       | `(add1 j-1)`      |
|--------------|-----------|-------------------|
| `0`          | `Trivial` | `Absurd`          |
| `(add1 n-1)` | `Absurd`  | `(= Nat n-1 j-1)` |

```lisp
(claim =consequence
  (→ Nat Nat
    U))

(define =consequence
  (λ (n j)
    (which-Nat n
      (which-Nat j
        Trivial ; (= 0 0)
        (λ (j-1)
          Absurd)) ; (= 0 (add1 j-1))
      (λ (n-1)
        (which-Nat j
          Absurd ; (= (add1 n-1) 0)
          (λ (j-1)
            (= Nat n-1 j-1))))))) ; (= (add1 n-1) (add1 j-1))
```

## `(=consequence-same)`

两个 `n` 显然是相同的。

```lisp
(claim =consequence-same
  (Π ((n Nat))
    (=consequence n n)))

(define =consequence-same
  (λ (n)
    (ind-Nat n
      (λ (k)
        (=consequence k k))
      sole
      (λ (n-1 =consequence_n-1)
        (same n-1)))))
```

- `base`：`(=consequence 0 0)`，即 `Trivial`
- `step`：其类型如下
    ```lisp
    (Π ((n-1 Nat))
    (→ (=consequence n-1 n-1)
        (=consequence (add1 n-1) (add1 n-1))))
    ```

    而 `(=consequence (add1 n-1) (add1 n-1))` 为 `(same n-1)`

# Types & Judgments

> **Imagine That ...**
>
> Using types, it is possible to assume things that may or may not be true, and then see what can be concluded from these assumptions.

类型（Type）应该被看作一种命题，所以可以有真命题也可以有假命题。所以前面函数的参数可以是 `(= 39 17)`，尽管这样的类型构造不出来 Proof，但是仍然可以将其作为函数的输入，从而构建一些值（如 `Absurd`），类似于基于一定的假设构建命题（但是如果假设是错误的，那么构造出来也无法被调用，因为没有合适的参数内传递进去）。所以类型可以是 Assumptions。

而 Judgments 则是最基本的、永真的。

## Sameness & Equality

> **Sameness versus Equality**
>
> Either two expressions are the same, or they are not. It is impossible to prove that they are the same because sameness is a judgment, not a type, and a proof is an expression with a specific type.

二者的区别如下：
- Sameness 是一种 judgment，Equality 是一种 Type
- 描述 Sameness 时不需要提供 evidence，描述 Equality 时必须要提供 evidence
- Sameness 的判定可以通过 the Laws and Commandments 完成；而 Equality 必须要通过 Proof，并且更难
- Equality 可以描述的范围比 Sameness 大（more things are equal than are the same）

个人想法：Sameness 可以由计算机自动判定，而 Equality 需要 proof，以及 creativity, ingenuity, and hard work。

由此可以发现 Judgements 一定是真的，而 Types 可以是假的，即我们可以“自由”地创造一些 Types。

# `use-Nat=`

这里用了一个 trick，类似于 Logical Foundations - Basics 里面的 contradictory in case analysis 介绍的，遇到矛盾时通过 `rewrite` 来结束讨论。

```lisp
(claim use-Nat=
  (Π ((n Nat)
      (j Nat))
    (→ (= Nat n j)
      (=consequence n j))))

(define use-Nat=
  (λ (n j)
    (λ (n=j)
      (replace n=j ; rewrite n=j in (=consequence n n)
        (λ (k)
          (=consequence n k))
        (=consequence-same n))))) ; 即 (=consequence n n)
```

`replace` 的作用是将 `(=consequence n n)` 中的第二个 `n` 换成 `j`。由此，我们就构造出了 `(=consequence n j)`。

并不用担心这样会构建出非法的类型（例如 `(= 0 1)`）。假如构建出了 `0=1`，那么 `n=j` 为 `0=1`。然而这样的参数是构造不出来的，所以这种情况也不可能发现。我们在不违背逻辑的情况下描述了结果为 `Absurd` 的命题。

## `zero-not-add1`

```lisp
(claim zero-not-add1
  (Π ((n Nat))
    (→ (= Nat zero (add1 n))
      Absurd)))

(define zero-not-add1
  (λ (n)
    (use-Nat= zero (add1 n))))
; (use-Nat= zero (add1 n))
; => (→ (= Nat zero (add1 n))
;      (=consequence zero (add1 n)))
; => (→ (= Nat zero (add1 n))
;      Absurd)
```

随便定义一个假命题：

```lisp
(claim donut-absurdity
  (→ (= Nat 0 6)
    (= Atom 'powdered 'glazed)))

(define donut-absurdity
  (λ (zero=six)
    (ind-Absurd
      (zero-not-add1 5 zero=six)
      (= Atom 'powdered 'glazed))))
```

> If there were evidence that “0 equals 6”, then there would be evidence for anything at all, including strange facts about donuts.

## `sub1`

> For every two Nats `n` and `j`, if `(add1 n)` equals `(add1 j)`, then `n` equals `j`.

```lisp
(claim sub1=
  (Π ((n Nat)
      (j Nat))
    (→ (= Nat (add1 n) (add1 j))
      (= Nat n j))))

(define sub1=
  (λ (n j)
    (use-Nat= (add1 n) (add1 j))))
```

`sub1` 可以用来定义 `1 != 6`：

```lisp
(claim one-not-six
  (→ (= Nat 1 6)
    Absurd))

(define one-not-six
  (λ (one=six)
    (zero-not-add1 4
      (sub1= 0 5 one=six))))
```

# `front`

`Absurd` 在其他方面也有应用，例如下面这个类似于 `head` 的函数：

```lisp
(claim front
  (Π ((E U)
      (n Nat))
    (→ (Vec E (add1 n))
      E)))
```

然而下面这个定义是错误的：

```lisp
(define front'
  (λ (E l es)
    (ind-Vec (add1 l) es
      (λ (k xs)
        E)
      ; ???
      (λ (k h t frontys)
        h))))
```

因为根据 motive，`ind-Vec` 应该返回 `E`。但是对 `base` 而言 `es` 为 `vecnil`，此时无法造出一个 `E` 类型的值（虽然由于 `(add1 l)` 的长度限制，不可能出现这种情况）。

## motive

下面通过更改 motive 的定义来解决这个问题。

```lisp
(claim mot-front
  (Π ((E U)
      (k Nat))
    (→ (Vec E k)
      U)))

(define mot-front
  (λ (E)
    (λ (k es)
      (Π ((j Nat))
        (→ (= Nat k (add1 j))
          E)))))
```

新的 motive 多了两个参数：`j` 和一个类型 `(= Nat k (add1 j))`。对于 `base` 而言，由于 `k` 为 `zero`，所以不存在对应的 `j` 使得 `(= Nat k (add1 j))`。这个和 `zero-not-add1` 有点像，所以 `base` 为：

```lisp
(λ (j eq)
  (ind-Absurd
    (zero-not-add1 j eq)
    E))
```

实际上计算时是不可能用到 `base` 的。

## `step`

`step` 的返回类型为：

```lisp
(mot-front E
  (add1 l)
  (vec:: e es))
; 即
; (Π ((j Nat))
;   (→ (= Nat (add1 l) (add1 j))
;     E))
```

与 `base` 不同的是，`step` 一定只要返回头元素即可。

```lisp
(claim step-front
  (Π ((E U)
      (l Nat)
      (e E)
      (es (Vec E l)))
    (→ (mot-front E
        l
        es)
      (mot-front E
        (add1 l)
        (vec:: e es)))))

(define step-front
  (λ (E l e es)
    (λ (front_es)
      (λ (j eq)
        e))))
```

## `front`

注意，`ind-Vec` 的结果是一个函数，所以要把对应的参数传入：

```lisp
(Π ((j Nat))
  (→ (= Nat (add1 l) (add1 j)))
    E)
```

`(add1 l)` 与 `(add1 j)` 相同，所以 `j` 为 `l`，`(= Nat (add1 l) (add1 j))` 为 `(same (add1 l))`。

```lisp
(define front
  (λ (E l es)
    ((ind-Vec (add1 l) es
      (mot-front E)
      (λ (j eq)
        (ind-Absurd
          (zero-not-add1 j eq)
          E))
      (step-front E))
    l (same (add1 l)))))
```

# 排中律

> Every statement is true or false. -- the Principle of the Excluded Middle / tertium non datur

下面尝试对排中律进行证明。（然后会发现无法证明）

```lisp
(claim pem
  (Π ((X U))
    (Either
      X
      (→ X Absurd))))
```

因为假设一个函数能够证明排中律，那么用这个函数可以证明出任何类型。（因为要构建一个 `Either`，就必须要指出它是 `left` 还是 `right`，这样就相当于必须给出命题的结论）

但是可以证明排中律一定不是错的。

## `pem-not-false`

> “Every statement is true or false“ can’t possibly be false.

```lisp
(claim pem-not-false
  (Π ((X U))
    (→ (→ (Either
            X
            (→ X Absurd))
        Absurd)
      Absurd)))
```

下面考虑怎么构建这个证明。

```lisp
(define pem-not-false
  (λ (X)
    (λ (pem-false)
      ???))) ; 要推出 Absurd

; pem-false 是
; (→ (Either
;     X
;     (→ X Absurd))
;   Absurd)
```

考虑要从 `pem-false` 推出一个 `Absurd`，所以应该给 `pem-false` 传入参数。

```lisp
(define pem-not-false
  (λ (X)
    (λ (pem-false)
      (pem-false ???)))) ; (Either X (→ X Absurd))
```

这个参数不能是 `left`，因为如果要用 `left` 那么就要给出 `X` 的证据，所以应该考虑用 `right`。

```lisp
(define pem-not-false
  (λ (X)
    (λ (pem-false)
      (pem-false
        (right
          (λ (x)
            ???)))))) ; Absurd
```

现在要构造一个 `Absurd`，前面能产生 `Absurd` 的只有 `pem-false`。

```lisp
(define pem-not-false
  (λ (X)
    (λ (pem-false)
      (pem-false
        (right
          (λ (x)
            (pem-false
              ???))))))) ; (Either X (→ X Absurd))
```

这个时候可以用 `left` 了。因为 `(→ X Absurd)` 假设了 `x` 是成立的，此时会推出 `Absurd`。而在前面没有这个假设，所以不能用。

```lisp
(define pem-not-false
  (λ (X)
    (λ (pem-false)
      (pem-false
        (right
          (λ (x)
            (pem-false
              (left x))))))))
```

# Decidable & Undecidable

> A statement is not false is less interesting than evidence that it is true.

一个命题不是错的，并不能说他是对的。

可以被判断对错的命题被称为 decidable 的命题。

```lisp
(claim Dec
  (→ U
    U))

(define Dec
  (λ (X)
    (Either
      X
      (→ X Absurd))))
```

可以发现，排中律可以等价表述为：所有的命题都是可判定的。

> pem ~ All statements are decidable.

```lisp
(claim pem
  (Π ((X U))
    (Dec X)))
```