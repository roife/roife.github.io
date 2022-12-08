---
layout: "post"
title: "「The Little Typer」 12 Even Numbers can be Odd"
subtitle: "偶数与奇数"
author: "roife"
date: 2021-04-04

tags: ["The Little Typer@读书笔记", "读书笔记@Tags", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "Pie@编程语言", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 偶数: `Even`

> There is some number that, added to itself, yields the original number.

可以用 Σ 表达。

```lisp
(claim Even
  (→ Nat
    U))

(define Even
  (λ (n)
    (Σ ((half Nat))
      (= Nat n (double half)))))
```

这里之所以用 `double` 而不用 `twice` 是因为，在之前已经看到如果用了 `twice`，那么 `(twice (add1 x))` 会变成 `(add1 (+ x (add1 x)))`；而 `(double x)` 则会变成 `(add1 (add1 (+ x x)))`。前者的第二个 `add1` 在内层，处理的时候往往要将其提取出来，显得更麻烦。

`0` 是偶数：

```lisp
(claim zero-is-even
  (Even 0))

(define zero-is-even
  (cons 0
    (same 0)))
```

# `+two-even`

一个偶数加上 `2`，结果还是一个偶数。

```lisp
; For every natural number n, if n is even, then 2 + n is even.
(claim two-even
  (Π ((n Nat))
    (→ (Even n)
      (Even (+ 2 n)))))
```

如果 `n` 满足 `(Even a)`，即 `(cons a (same n))`。则对 `(Even (+ 2 n))` 为 `(cons (add1 a) (same (+ 2 n))))`。

```lisp
(define two-even
  (λ (n e_n)
    (cons (add1 (car e_n))
      (cong (cdr e_n) (+ 2)))))
; 这里的 (cong (cdr e_n) (+ 2)) 不能直接写 (same (+ 2 n))
; 因为 (add1 a) 是从 Σ type 里面拆出来的，不能脱离了后面的命题单独使用（即失去证明）
```

# 奇数：`Odd`

> Odd numbers cannot be split into two equal parts. There is always an add1 remaining.

```lisp
(claim Odd
  (→ Nat
    U))

(define Odd
  (λ (n)
    (Σ ((haf Nat))
      (= Nat n (add1 (double haf))))))
```

13 是一个奇数：

```lisp
(claim thirteen-is-odd (Odd 13))

(define thirteen-is-odd
  (cons 6
    (same 13)))
```

## `add1-even→odd`

偶数加一会变成奇数。

证明的时候考虑 `Odd` 的定义，对于一个偶数 `n`，`(Even n)` 和 `(Odd n)` 的一半都是 `(car e_n)`。

```lisp
(claim add1-even→odd
  (Π ((n Nat))
    (→ (Even n)
      (Odd (add1 n)))))

(define add1-even→odd
  (λ (n e_n)
    (cons (car e_n)
      (cong (cdr e_n) (+ 1)))))
```

## `add1-odd→even`

证明的时候可以先写出已有的条件和要证明的目标。

```lisp
; o_n 的条件
(= Nat
  n
  (add1 (double (car on))))

; 要证明的
(= Nat
  (add1 n)
  (double (add1 (car o_n))))
; 即
(= Nat
  (add1 n)
  (add1
    (add1
      (double (car o_n)))))
```

```lisp
(claim add1-odd→even
  (Π ((n Nat))
    (→ (Odd n)
      (Even (add1 n)))))

(define add1-odd→even
  (λ (n o_n)
    (cons (add1 (car o_n))
      (cong (cdr o_n) (+ 1)))))
```

# Ackermann

```lisp
(claim repeat
  (→ (→ Nat
        Nat)
      Nat
    Nat))

(define repeat
  (λ (f n)
    (iter-Nat n
      (f 1)
      (λ (iter_f,n-1)
        (f iter_f,n-1)))))

(claim ackermann
  (→ Nat Nat
    Nat))

(define ackermann
  (λ (n)
    (iter-Nat n
      (+ 1)
      (λ (ackermann_n-1)
        (repeat ackermann_n-1)))))
```