---
layout: "post"
title: "「The Little Typer」 13 Even Haf a Baker's Dozen"
subtitle: "Either"
author: "roife"
date: 2021-04-04

tags: ["The Little Typer@读书笔记", "读书笔记@Tags", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "Pie@编程语言", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# `Either`

> **The Law of Either**
>
> `(Either L R)`is a type if `L` is a type and `R` is a type.
>
> **注解**：其实就是逻辑里面的 Or 运算，如果 `L` 成立或者 `R` 成立，那么 `L || R` 成立。

`(Either L R)` 有两个 constructor，分别是 `left` 和 `right`。如果 `lt` 是 `L`，`rt` 是 `R`，那么 `(left lt)` 和 `(right rt)` 都是 `(Either L R)`。

`left` 和 `right` 用来指定 evidence 符合哪一侧的条件，从而*构建* Either 类型。

> **The Law of `left`**
>
> `(left lt)` is an `(Either L R)` if `lt` is an `L`.

> **The Law of `right`**
>
> `(right rt)` is an `(Either L R)` if `rt` is an `R`.

如果 `lt_1` 和 `lt_2` 都是相同的 `L`，那么 `(left lt_1)` 和 `(left lt_2)` 都是相同的 `(Either L R)`。对于 `rt` 同理。

# `ind-Either`

`ind-Either` 是 `Either` 的 eliminator。其特殊之处在于 `ind-Either` 有两个 `base`，而没有 `step`。这是因为之前的大部分 constructor 的都是递归定义的，例如：对于 `(add1 x)` 而言，`x` 也是一个 Nat；对于 `(:: x y)` 而言，`y` 是一个 List。而 `Either` 不是递归定义的的，`(left x)` 中的 `x` 不一定是 `Either` 类型的，所以不能用 `step`，`ind-Either` 也不能递归调用。

`ind-Either` 的使用格式为：

```lisp
(ind-Either target
  mot
  base-left
  base-right)
```

其中，`mot` 的类型为：

```lisp
(→ (Either L R)
  U)
```

`base-left` 和 `base-right` 都是 Σ type：

```lisp
; base-left
(Π ((x L))
  (mot (left x)))

; base-right
(Π ((y R))
  (mot (right y)))
```

> **The Law of `ind-Either`**
>
> If target is an `(Either L R)`, `mot` is an
>
> ```lisp
> (→ (Either L R)
>   U)
> ```
>
> `base-left` is a
>
> ```lisp
> (Π ((x L)) ; 注意不是 Σ
>   (mot (left x)))
> ```
>
> and `base-right` is a
>
> ```lisp
> (Π ((y R))
>   (mot (right y)))
> ```
>
> then
>
> ```lisp
> (ind-Either target
>   mot
>   base-left
>   base-right)
> ```
>
> is a `(mot target)`.
>
> **注解**：相当于分类讨论，如果 target 是*左边的类型*或者是*右边的类型*

> `base-left`/`base-right` explains how the motive is fulfilled for every `left`/`right`
>
> **注解**：`base-left`/`base-right` **也是函数**，传入原来的 L/R 来构建新类型

如果 `target` 是 `(left x)`，那么结果就是 `base-left`；如果 `target` 是 `(right y)`，那么结果就是 `(right y)`。

> **The First Commandment of `ind-Either`**
>
> ```lisp
> (ind-Either (left x)
>   mot
>   base-left
>   base-right)
> ```
>
> is the same `(mot (left x))` as `(base-left x)`.

> **The Second Commandment of `ind-Either`**
>
> ```lisp
> (ind-Either (right y)
>   mot
>   base-left
>   base-right)
> ```
>
> is the same `(mot (right y))` as `(base-right y)`.

# `even-or-odd`

证明自然数要么是奇数，要么是偶数。
考虑外层用 `ind-Nat` 归纳，`step` 用 `ind-Either` 构建。

```lisp
(claim even-or-odd
  (Π ((n Nat))
    (Either (Even n) (Odd n))))

(claim mot-even-or-odd
  (→ Nat
    U))

(define mot-even-or-odd
  (λ (k)
    (Either (Even k) (Odd k))))

(claim step-even-or-odd
  (Π ((n-1 Nat))
    (→ (mot-even-or-odd n-1)
      (mot-even-or-odd (add1 n-1)))))

(define step-even-or-odd
  (λ (n-1)
    (λ (e-or-o_n-1) ; e-or-o_n-1 为 (Either (Even n-1) (Odd n-1))
      (ind-Either e-or-o_n-1
        (λ (e-or-o) ; 这里的 mot 用不到 e-or-o
          (mot-even-or-odd (add1 n-1))) ; ind-Either 的 mot 用的是之前定义的函数，是因为这里的 mot 的类型就是 step 的返回值类型
        (λ (e_n-1)
          (right
            (add1-even→odd n-1 e_n-1)))
        (λ (e_n-1)
          (left
            (add1-odd→even n-1 e_n-1)))))))

(define even-or-odd
  (λ (n)
    (ind-Nat n
      mot-even-or-odd
      (left zero-is-even) ; zero-is-even 是左侧类型的证明，即 Even 的 evidence
      step-even-or-odd)))
```

这里的关键是 `step` 函数的理解。`step` 函数主体是 `ind-Either`，其中由三部分组成：`mot`、`base-left`、`base-right`。

其中 `mot` 决定了 `ind-Either` 的返回类型。`step` 的返回类型是一个 `(Either (Even k) (Odd k))`，即 `(mot e-or-o_n-1)` 的类型也是这个，这里用不到 `e-or-o_n-1` 或者其他传入的类型。

考虑 `base-left`，其类型为：

```lisp
; (Π ((x L))
;   (mot (left x)))
; 令 L 为 (Even n-1)
; 则根据 Either 的定义，(left x) 为 (Either (Even n-1) (Odd n-1))
(→ (Even n-1) ; → 是特殊的 Π
  (Either
    (Even (add1 n-1))
    (Odd (add1 n-1))))
```

容易想到使用 `add1-even→odd`。

## 证明：`(even-or-odd 2)`

1.
```lisp
(even-or-odd 2)
```

2.
```lisp
(ind-Nat 2
  mot-even-or-odd
  (left zero-is-even)
  step-even-or-odd)
```

3.
```lisp
(step-even-or-odd
  1
  (ind-Nat 1
    mot-even-or-odd
    (left zero-is-even)
    step-even-or-odd))
```


4.
```lisp
((λ (n-1)
  (λ (e-or-o_n-1)
    (ind-Either e-or-on-1
      (λ (e-or-o_n-1)
        (mot-even-or-odd (add1 n-1)))
      (λ (e_n-1)
        (right
          (add1-even→odd n-1 e_n-1)))
      (λ (o_n-1)
        (left
          (add1-odd→even n-1 o_n-1))))))
  1
  (ind-Nat 1 ... )) ; 省略 ind-Nat 的部分
```

5.
```lisp
((λ (e-or-o_n-1)
  (ind-Either e-or-o_n-1
    (λ (e-or-o_n-1)
      (mot-even-or-odd 2))
    (λ (e_n-1)
      (right
        (add1-even→odd 1 e_n-1)))
    (λ (o_n-1)
      (left
        (add1-odd→even 1 o_n-1)))))
  (ind-Nat 1 ... ))
```

6.
```lisp
(ind-Either (ind-Nat 1 ... )
  (λ (e-or-o_n-1)
    (mot-even-or-odd 2))
  (λ (e_n-1)
    (right
      (add1-even→odd 1 e_n-1)))
  (λ (o_n-1)
    (left
      (add1-odd→even 1 o_n-1))))
```

7.
```lisp
(ind-Either (step-even-or-odd 0 (ind-Nat 0 ...))
  (λ (e-or-o_n-1)
    (mot-even-or-odd 2))
  (λ (e_n-1)
    (right
      (add1-even→odd 1 e_n-1)))
  (λ (o_n-1)
    (left
      (add1-odd→even 1 o_n-1))))
```

8.
```lisp
(ind-Either (step-even-or-odd 0 (left zero-is-even))
  (λ (e-or-o_n-1)
    (mot-even-or-odd 2))
  (λ (e_n-1)
    (right
      (add1-even→odd 1 e_n-1)))
  (λ (o_n-1)
    (left
      (add1-odd→even 1 o_n-1))))
```

9.
```lisp
(ind-Either (right (add1-even→odd 0 zero-is-even))
  (λ (e-or-o_n-1)
    (mot-even-or-odd 2))
  (λ (e_n-1)
    (right
      (add1-even→odd 1 e_n-1)))
  (λ (o_n-1)
    (left
      (add1-odd→even 1 o_n-1))))
```

10.
```lisp
(left
  (add1-odd→even 1
    (add1-even→odd 0
      zero-is-even)))
```

这个结果已经是一个 value 了。

首先由于 top constructor 是 `left`，所以说明 `(Even 2)` 成立。

下面寻找其 Normal Form，考虑展开 `add1-odd→even` 这两个函数以及 `zero-is-even`。

11.
```lisp
(left
  ((λ (n_1 o_n)
    (cons (add1 (car o_n))
      (cong (cdr o_n) (+ 1))))
    1
    ((λ (n_2 e_n)
      (cons (car e_n)
        (cong (cdr e_n) (+ 1))))
      0
      (cons 0 (same 0)))))
```

12.
```lisp
(left
  ((λ (o_n)
    (cons (add1 (car o_n))
      (cong (cdr o_n) (+ 1))))
    ((λ (e_n)
      (cons (car e_n)
        (cong (cdr e_n) (+ 1))))
      (cons 0 (same 0)))))
```

13.
```lisp
(left
  ((λ (o_n)
    (cons (add1 (car o_n))
      (cong (cdr o_n) (+ 1))))
    (cons 0
      (cong (same 0) (+ 1)))))
```

14.
```lisp
(left
  ((λ (o_n)
    (cons (add1 (car o_n))
      (cong (cdr o_n) (+ 1))))
    (cons 0
      (same 1))))
```

15.
```lisp
(left
  (cons 1
    (cong (same 1) (+ 1))))
```

16.
```lisp
(left
  (cons 1
    (same 2)))
```

从这个 Normal Form 可以看到，`even-or-odd` 起到了两个作用：
- `even-or-odd` as a proof：证明每个 Nat 都是 Even 或者 Odd，此时它是一个 statement 的 evidence
- `even-or-odd` as a function：寻找一个 haf 使得 Even 或者 Odd 成立，此时它是一个 result