---
layout: "post"
title: "「The Little Typer」 04 Easy as Pie"
subtitle: "Pi Type & Polymorphism"
author: "roife"
date: 2021-03-03

tags: ["The Little Typer@读书笔记", "读书笔记@Tags", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "Pie@编程语言", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# Pi Type：Π

Π 表达式可以用于编写泛型 lambda 表达式的类型声明，并且用于参数化类型。

```lisp
(claim flip
  (Π ((A U)
      (D U))
    (→ (Pair A D)
      (Pair D A))))

(define flip
  (λ (A D)
    ((λ (p)
      (cons (cdr p) (car p)))))
```

在定义的过程中，无论是 `claim` 还是 `define` 中的 `A` 和 `D` 都只是一个符号，表示一种类型，没有特殊的意义，也不需要相互对应。（不过一般 `claim` 和 `define` 中的参数化类型的符号会相同）

> **The Intermediate Law of Application**
>
> If `f` is a
>
> ```lisp
> (Π ((Y U))
>   X)
> ```
>
> and `Z` is a U, then `(f Z)` is an `X`, and every `Y` in `X` has been consistently replaced by `Z`.
>
> **注解**：Π Type 相当于全称量词，因为 Pie 中的函数都是 total function，所以 Π 表达式的参数可以传入对应类型任意的值，它们都可以使类型成立，即其类型为 $\forall\ a:Y, X[Y:=a]$

Π 表达式和 → 表达式都可以**描述 λ 表达式的类型**，区别在于传入参数后表达式的类型。Π 表达式传入全部参数后返回一个 → 表达式。

## `elim-Pair`

- `(elim-Pair A D X p f)`：将一个 `(Pair A D)` `p` 拆分成两个元素传入函数 `f`，返回值为 `X`

```lisp
(claim elim-Pair
  (Π ((A U)
      (D U)
      (X U))
    (→ (Pair A D)
        (→ A D
        X)
      X)))

(define elim-Pair
  (λ (A D X)
    (λ (p f)
      (f (car p) (cdr p)))))
```

## `twin`

- `(twin Y x)`：传入一个 `Y` 类型的 `x`，返回 `(cons x x)`

```lisp
(claim twin
  (Π ((Y U))
    (→ Y
      (Pair Y Y))))

(define twin
  (λ (Y)
    (λ (x)
      (cons x x))))
```


## Π 表达式 Curry

Π 表达式也可以进行类似于 Curry-ing 的操作：

```lisp
(claim twin-Atom
  (→ Atom
    (Pair Atom Atom)))

(define twin-Atom
  (twin Atom)) ; 返回一个函数
```