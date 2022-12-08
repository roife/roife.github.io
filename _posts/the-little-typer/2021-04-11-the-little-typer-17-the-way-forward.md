---
layout: "post"
title: "「The Little Typer」 17 The Way Forward"
subtitle: "DT 语言的更多特性"
author: "roife"
date: 2021-04-11

tags: ["The Little Typer@读书笔记", "读书笔记@Tags", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "Pie@编程语言", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

- infinitely many universes
- the ability to define new type constructors and their associated data constructors
- the ability to define functions through pattern matching
- the ability to leave out expressions that the language can find on its own
- tactics for automating proof construction.

# A Universe Hierarchy

本书中只遇到了一个 universe type：`U`。`U` 既不能描述自己（即不可以用 `U:U`），也不能被其他类型包含（不可以用 `(List U)`）。

然而在成熟的 DT 语言中，会存在一个类型去描述 `U`，即 `U : U1`，甚至还可以定义 `U1 : U2`。由此形成了一个 Universe Hierarchy。

# Inductive Datatypes

成熟的 DT 语言一般可以自定义归纳类型与相应的构造子。如下面这样的对于 `(List E)` 的定义：

```lisp
(data List ((E U)) () ; 第一个是 parameters，第二个是 indices
  (nil ()
    (List E))
  (:: ((e E) (es (List E)))
    (List E))
  ind-List)
```

```lisp
(data Less-Than () (( j Nat) (k Nat))
  (zero-smallest ((n Nat))
    (Less-Than zero (add1 n)))
  (add1-smaller ((j Nat)
                 (k Nat)
                 (j<k (Less-Than j k)))
    (Less-Than (add1 j) (add1 k)))
  ind-Less-Than)
```

> **The Law of `ind-Less-Than`**
>
> if target is a `(Less-Than j k)`,
>
> `mot` is a
>
> ```lisp
> (Π ((j Nat) (k Nat))
>   (→ (Less-Than j k) U))
> ```
>
> `base` is a
>
> ```lisp
> (Π ((k Nat)
>     (lt (Less-Than zero (add1 k))))
>   (mot zero k lt))
> ```
>
> `step` is a
>
> ```lisp
> (Π ((j Nat)
>     (k Nat)
>     (j<k (Less-Than j k)))
>   (→ (mot j k j<k)
>     (mot (add1 j) (add1 k)
>       (add1-smaller j k j<k))))
> ```
>
> then `(ind-Less-Than target mot base step)` is a `(mot j k target)`

# Recursive Functions with Pattern Matching

在 DT 中，一般要求递归函数进行递归时，递归运算要发生在 smaller values 上。即每次递归都使得某个量变小，最终保证递归会终止。

模式匹配也是一种定义安全递归函数的方法，而且显得更加直观：

```lisp
(claim length
  (Π ((E Nat))
    (→ (List E) Nat)))

(define length
  (λ (E es)
    (match es
      (nil zero)
      ((:: x xs) (add1 (length xs))))))
```

```lisp
(claim front
  (Π ((E U)
      (n Nat))
    (→ (Vec E (add1 n)) E)))

(define front
  (λ (E n es)
    (match es
      ((vec:: x xs) x))))
```

成熟的 DT 语言一般会允许自己定义递归函数，并且进行 termination check 以保证递归会终止。

# Implicit Arguments

即省略不必要的类型参数，让语言自动推导。

Pie 中也有类似的机制：
1. `Π∗`：an implicit `Π`
2. `λ∗`：an implicit `λ`
3. `implicitly`：an implicit function application, its arguments as filling an implicit rather than explicit role（即表明是显式写出 implicit arguments）

```lisp
(claim length
  (Π∗ ((E U))
    (→ (List E) Nat)))

(define length
  (λ∗ (E)
    (λ (es)
      (rec-List es
        0
        (λ (e es l)
          (add1 l))))))

; (length (:: 'potato (:: 'gravy nil)))
; (length Atom (:: 'potato (:: 'gravy nil)))

; (implicitly length Atom)
; (→ (List Atom) Nat)
```

# Proof Tactics

> A tactic is a program in a special language that is provided with a desired type (called a goal) that either succeeds with zero or more new goals or fails.

```lisp
(claim even-or-odd
  (Π ((n Nat))
    (Either (Even n) (Odd n))))

(define-tactically even-or-odd
  (intro n)
  (elim n)
  (apply zero-is-even)
  (intro n-1 e-or-on-1)
  (elim e-or-on-1)
  (then
    right
    (apply add1-even→odd)
    auto)
  (then
    left
    (apply add1-odd→even)
    auto))
```

