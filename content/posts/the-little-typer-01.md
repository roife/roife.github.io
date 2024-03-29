+++
title = "[The Little Typer] 01 The More Things Change, the More They Stay the Same"
author = ["roife"]
date = 2021-02-28
series = ["The Little Typer"]
tags = ["Dependent Type", "形式化验证", "Pie", "类型系统", "程序语言理论"]
draft = false
+++

## Atom {#atom}

一个单引号 `'` 开头，后面跟着的是字母或者连词符 `-` 的符号被称为 `Atom`，如 `'atom` 或者 `'---`，但是注意不能有数字。

> **(The Law of Tick Marks)**
>
> A tick mark directly followed by one or more letters and hyphens is an `Atom`.


## Pair {#pair}

`(cons 'a 'b)` 的第一部分（`'a`）被称为 `car`，第二部分（`'b`）被称为 `cdr`（注意这里和 Lisp 不同，`cons` 只能用于二元组）。

一个 `Pair` 由 `cons`、`car` 和 `cdr` 这三部分组成。

如果 car 和 cdr 是相同的 Atom，则称为两个表达式“is the same `(Pair Atom Atom)`”。


## Judgments {#judgments}

-   Judgments 1：**<span class="underline">\_\_</span> is a <span class="underline">\_\_</span>.**，用来判断类型，例如 `'courgette is an Atom.`。
    -   Judgments 可以是对的，也可以是错的。

-   Judgments 2：`____ is the same ____ as ____.`，例如 `'citron is the same Atom as 'citron.`。

    -   Judgement 2 的第二个空也必须填 type。

    > **(The Commandment of Tick Marks)**
    >
    > Two expressions are the same Atom if their values are tick marks followed by identical letters and hyphens.

-   Judgments 3：`____ is a type.`，用来描述另一个表达式的表达式被称为类型 **type**，形如 `Atom` 或者 `(Pair Atom Atom)`，如 `Atom is a type.`。

    > **(The Law of Atom)**
    >
    > Atom is a type.

-   Judgments 4：`____ and ____ are the same type.`，判断两个类型是否相同，`____ and ____ are the same type.`，如 `Atom and Atom are the same type.`
    -   进行 Judgement 4 之前，必须保证两个都是 `Type`。即 `A and B are the same type.` 的前提条件是 `A is a type` 且 `B is a type`。


## Normal Forms {#normal-forms}


### 定义 {#定义}

Normal Forms 是指描述一个表达式的最简单的形式，注意描述时必须要带上类型。例如：

> `'olive-oil` is the normal form of the Atom
>
> ```lisp
> (car
>   (cdr
>     (cons 'ratatouille
>       (cons ('baguette 'olive-oil)))))
> ```
>
> `(cons 'ratatouille 'baguette)` is a normal `(Pair Atom Atom)`

<div class="question">

**所有的表达式都有 Normal Form 吗？**

</div>

<div class="answer">

在不给定类型的情况下讨论是否有 normal form 是没有意义的。但是对于每一个可以用类型描述的表达式，都有一个由该类型所决定的 normal form。

</div>

我们可以通过比较两个表达式的 normal form 来判断它们是否相同（sameness）。

<div class="definition">

**(Normal Forms)**

Given a type, every expression described by that type has a **normal form**, which is the most direct way of writing it. If two expressions are the same, then they have identical normal forms, and if they have identical normal forms, then they are the same.

**注解**：Sameness 由 Normal Forms 决定

</div>


### Normal Forms 与 Types {#normal-forms-与-types}

如果一个表达式和某个类型为 `(Pair Atom Atom)` 的表达式相同，那么它也是一个 `(Pair Atom Atom)`。

> **(Normal Forms and Types)**
>
> Sameness is always accoding to a type, so normal forms are also **determined by a type**.
>
> **注解**：Normal Forms 是由 Type 决定的，即 **the most direct** 的形式是由 Type 决定的

比较 `cons` 表达式是否相同，只要它们都由 `cons` 开头，并且它们的 `car` 和 `cdr` 相同。

> **(The Fist Commandment of `cons`)**
>
> Two `cons`-expressions are the same `(Pair A D)` if their cars are the same `A` and their cdrs are the same `D`. Here, `A` and `D` stand for any type.


### Normal Forms of Types {#normal-forms-of-types}

<div class="definition">

**(ill-typed)** 既不能被类型描述，本身也不是类型的式子称为 ill-typed。

</div>

对于 `(Pair A B)`，只有 `A` 和 `B` 本身都是类型时，`Pair` 才是一个类型，如：

````lisp
(Pair
  (cdr
    (cons Atom 'olive))
  (car
    (cons 'oil Atom)))
;; 结果是 (Pair 'olive 'oil)，本身不是一个类型，而且它不能被类型描述，所以没有 normal forms

(Pair
  (cdr
    (cons Atom 'olive))
  (car
    (cons 'oil Atom)))
;; 等价于 (Pair Atom Atom)
````

**注解**：这里可以发现 Type 可以和 Term 一起参与运算

类型也有 normal forms，并且定义和上面的类似。

<div class="definition">

**(Normal Forms of Types)**

Every expression that is a type has a normal form, which is the most direct way of writing that type. If two expressions are the same type, then they have identical normal forms, and if two types have identical normal forms, then they are the same type.

</div>


## 自然数 Nat {#自然数-nat}

如果 `n` 是 Nat，则 `(add1 n)` 也是 Nat。


### Claims {#claims}

在 Pie 中，`0` 可以写成 `zero`，则：

````lisp
(claim one
  Nat)

(define one
  (add1 zero))
````

在定义前必须要用 `claim` 来声明类型。

> **(Claims before Definitions)**
>
> Using define to associate a name with an expression requires that the expression's type has previously been associated with the name using claim.


### Contructors {#contructors}

Constructors 是用来构建新类型的工具，例如 Nat 的 `zero=/=add1` 或者 Pair 的 `cons`。


### Values {#values}

如果一个式子的顶端是一个 constructor（即 top constructor，对于 `one` 是 `add1`），那么它一个 Value。

<div class="definition">

**(Values / Canonical expressions)**

An expression with a constructor at the top is called a **value**.

</div>

对于一个 Value，如果 top constructor 的参数**都**是 normal 的，那么这个式子是 normal 的。例如 `zero` 是 normal，并且 `add1` 是 normal 的，所以 `one` 是 normal 的。

> **(Values and Normal Forms)**
>
> **Not every value is in normal form.** This is because the arguments to a constructor need not be normal.
>
> Each expression has only one normal form.
>
> ````lisp
> (add1
>   (+ (add1 zero)
>      (add1
>        (add1 zero))))
> ; 是 Value，但是不 normal
> ````


### Evaluation {#evaluation}

寻找一个 value 来描述表达式的过程被称为 evaluation（注意，不是 normal forms）。

> **(Everything Is an Expression)**
>
> In Pie, values are also expressions. Evaluation in Pie finds an expression, not some other kind of thing.
>
> **注解**：在 Pie 中，values 也是 expressions，evaluation 就是一个找 value 的过程，且这个 value 和 expression 是相同（same）的

一个 normal 的表达式应该是不可以被 evaluate 的。一般来说，并不需要将表达式化为 normal 的形式。


### Sameness of Nat {#sameness-of-nat}

如果两个 Nat 它们的某个 values 是相同的，那么它们就是相同的。

首先两个 `zero` 是相同的。如果两个 values 的 top constructor，且 arguments 是相同的，则它们是相同的。

> **(The Commandment of `zero`)**
>
> `zero` is the same Nat as `zero`.

<!--quoteend-->

> **(The Commandment of `add1`)**
>
> If `n` is the same Nat as `k`, then `(add1 n)` is the same Nat as `(add1 k)`.

当然，对于定义过的符号，不能重复定义。


## Sameness of Pair {#sameness-of-pair}

`(car (cons a d))` 的 value 是 **`a` 的 value**。同理，`(cdr (cons a d))` 的 value 是 **`d` 的 value**。

如果两个表达式是相同的 `(Pair Atom Nat)`，那么它们的 constructor 都是 `cons`，而且 `Atom` 和 `Nat` 部分相同。


## Types Constructors {#types-constructors}

所有的 atoms（例如 `'garlic`）都是 constructors，同时也是 values（它们的类型是 `Atom`）。

`zero` 是一个没有参数的 constructor，而 Nat 不是 constructors。后者描述了由 constructors 组成的式子。

> `zero` and `add1` are constructors that **create data**, while Nat **describes** data that is just `zero`, or data that has `add1` at its top and another Nat as its argument.

同理，Pair-expressions 描述了由 `cons` 这个 constructor 组成的式子。

但是 Pair 是一个 **type constructor**，它构成了一个类型。类似的，Nat 和 Atom 也是 type constructors。

`````lisp
(cons 'basil
  (cons 'thyme 'oregano))

; 类型如下
(Pair Atom
  (Pair Atom Atom))
`````
