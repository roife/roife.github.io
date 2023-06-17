+++
title = "[The Little Typer] 02 Doin' What Comes Naturally"
author = ["roife"]
date = 2021-03-01
series = ["The Little Typer"]
tags = ["Dependent Type", "形式化验证", "Pie", "类型系统", "程序语言理论"]
draft = false
+++

## Eliminators {#eliminators}

`cons` 是 constructor，`Pair` 是 type constructor，它们都用来构建值；而 `car` 这种用来分解值，称为 eliminator。Eliminators 可以使用 values（不单是可以用于提取内部的值，例如还可以用于归纳等）。

> **Constructors and Eliminators**
>
> Constructors build values, and eliminators take apart values built by constructors.


## λ：lambda {#λ-lambda}

λ 也是一个 constructor，可以构建 `(λ (x0 x ...) body)` 这样的 value。而对应的 eliminators 则是将 lambda 应用参数。

> **Eliminating Functions**
>
> Applying a function to arguments is the eliminator for functions.

对 λ 应用参数会产生替换，即 substitution。

```lisp
((λ (flavor) (cons flavor 'lentils))
  'garlic)
; (cons 'garlic 'lentils)
```

λ 嵌套时，内层参数可以屏蔽外层参数。

```lisp
((λ (root)
  (cons root
    (λ (root) root)))
  'carrot)

; 计算结果如下
(cons 'carrot
  (λ (root) root))
```


### λ 的类型：→ {#λ-的类型}

λ 的类型类似于 `(→ (Type0 Type ...) Body)`，其中 `Type` 表示参数类型，最后一个参数是返回类型。

```lisp
(→ Atom
  (Pair Atom Atom))
; 接受一个 Atom 参数，应用于 (Pair Atom Atom) 结构

; 下面是类型的一种等价表达
(→ (car (cons Atom 'pepper))
  (Pair (cdr (cons 'salt Atom)) Atom))
```

> **The Initial Law of Application**
>
> If `f` is an
>
> ```lisp
> (→ Y
>   X)
> ```
>
> and `arg` is a `Y`, then
>
> ````lisp
> (f arg)
> ````
>
> is an `X`.


### Sameness for λ values {#sameness-for-λ-values}

两个 λ 表达式如果参数数量和函数体相同，则它们相同，并且比较的过程中允许对参数进行“重命名”（alpha 变换）。

> **The Initial First Commandment of λ**
>
> Two λ-expressions that expect the same number of arguments are the same if their **bodies are the same** after **consistently renaming their variables** (alpha-conversion).

<!--quoteend-->

> **The Law of Renaming Variables**
>
> Consistently renaming variables can't change the meaning of anything.

<!--quoteend-->

> **The Initial Second Commandment of λ (eta-expansion)**
>
> If `f` is an
>
> `````lisp
> (→ Y X)
> `````
>
> then `f` is the same
>
> ``````lisp
> (→ Y
>   X)
> ``````
>
> as
>
> ```````lisp
> (λ (y)
>   (f y))
> ```````
>
> as long as `y` does not occur in `f`.


## Neutral Expressions {#neutral-expressions}

如果一个表达式如果不是 values（顶端是 eliminators），而且由于存在变量不能进行 evaluation，则被称为 **neutral expression**。

例如如果 `x` 的类型为 `(Pair Atom Atom)`，那么 `(cdr x)` 是 neutral expression。但是 `(cons y 'rutabaga)` 不是 natural expression，而是一个 value。

<div class="definition">

**(Neutral expression)**

Expressions that are not values and cannot yet be evaluated due to a variable are called **neutral**.

</div>


### Sameness of Neutral Expressions {#sameness-of-neutral-expressions}

两个表达式比较时可以进行 consistently renaming。例如：

> ````````lisp
> (λ (x)
>   (car x))
> ````````
>
> is the same
>
> `````````lisp
> (→ (Pair Nat Nat)
>   Nat)
> `````````
>
> as
>
> ``````````lisp
> (λ (y)
>   (car y))
> ``````````

如果两个 neutral expressions 的 top eliminator 是相同的，而且 eliminator 的参数都是相同的，那么它们是相同的。

> **The Commandment of Neutral Expressions**
>
> Neutral expressions that are written identically are the same, **no matter their type**.


## `define` {#define}

用 `define` 可以简化程序：

> **The Law and Commandment of `define`**
>
> Following `(claim name X)` and `(define name expr)`,
>
> if `expr` is an `X`,
>
> then `name` is an `X`
>
> and `name` is the same `X` as `expr`.

<!--quoteend-->

> **The Second Commandment of `cons`**
>
> If `p` is a `(Pair A D)`, then it is the same `(Pair A D)` as `(cons (car p) (cdr p))`.

使用 `define` 或 `claim` 定义名字时，不能与已有名字重复。

> **Names in Definitions**
>
> In Pie, only names that are not already used, whether for constructors, eliminators, or previous definitions, can be used with claim or define.


### which-nat {#which-nat}

`which-Nat` 是一个函数，它判断一个 Nat 是否是 `zero`。如果不是，它可以去掉 Nat 的 top constructor 并将其代入一个函数。

使用格式如下：

```````````lisp
(which-Nat target
  base
  step)
```````````

如果 `target` 是 `zero`，那么返回 `base`；否则只能是 `(add1 n)`，返回 `(step n)`。`which-Nat` 类似于一种**模式匹配**。

```````````lisp
(which-Nat zero
  'naught
  (λ (n) ; 这里的 n 是 unused names
    'more))
; 返回 'naught

(which-Nat 4
  'naught
  (λ (n)
    'more))
; 返回 'more
```````````

> **The Law of which-Nat**
>
> If `target` is a Nat, `base` is an `X`, and `step` is an
>
> ```````````lisp
> (→ Nat X)
> ```````````
>
> then
>
> ````````````lisp
> (which-Nat target
>   base
>   step)
> ````````````
>
> is an `X`.

<!--quoteend-->

> **The First Commandment of which-Nat**
>
> If
>
> `````````````lisp
> (which-Nat zero
>   base
>   step)
> `````````````
>
> is an `X`, then it is the same `X` as `base`.

<!--quoteend-->

> **The Second Commandment of which-Nat**
>
> If
>
> ``````````````lisp
> (which-Nat (add1 n)
>   base
>   step)
> ``````````````
>
> is an `X`, then it is the same `X` as `(step n)`.


## Recursion is not an option (Gauss function 1) {#recursion-is-not-an-option--gauss-function-1}

-   `(gauss n)`：计算 \\(0 + \cdots + n\\)

一个用递归写出来的版本可能是这样的：

```````````````lisp
(claim gauss
  (→ Nat
      Nat))

(define gauss
  (λ (n)
    (which-Nat n
      zero
      (λ (p)
        (+ (add1 p) (gauss p))))))
```````````````

但是我们这里不用递归，因为递归有可能会写出 expression without a value（例如死循环）。

那怎么写这个函数呢，这个问题留到以后解决。


## Types values {#types-values}

如果 Types 的 top constructor 是 **type constructor**，那么它是一个 value。比如 `Atom` 或 `(Pair Atom Atom)`，而 `(car (cons Atom 'prune))` 虽然是一个 type，但是不是 value。

<div class="definition">

**(Type Values)**

An expression that is described by a type is a value when it has a constructor at its top.

Similarly, an expression that is a type is a value when it has a **type constructor at its top**.

</div>

> **Type constructor &amp; Constructor 的区别**
>
> Type constructors 构建类型，而 constructors 构建值（value），值可以被类型所描述


## U: Universal Type {#u-universal-type}

Values 可以用 Types 来描述，而 Types 可以用 U 来描述。

-   `(cons 'plum 'plum)` is a `(Pair Atom Atom)`.
-   `(cons Atom Nat)` is a `(Pair U U)`, not a `U`.

> **Every U Is a Type**
>
> Every expression described by U is a type, but not every type is described by U.
>
> **注解**：U is a type, but U is not a U.（一个类型的类型不能是自己）

判断一个值是否是某个类型，那么需要知道这个类型所有的值。但是对于 `U` 而言，不可能知道所有的 type constructor，因为可以创建新的 type，因此也可以创建新的 type constructor。


### Pear {#pear}

通过 `U`，我们可以用 `define` 去定义类型 `Pear`：

```````````````lisp
(claim Pear
  U)

(define Pear
  (Pair Nat Nat))
```````````````

`Pear` 这样由 `define` 定义的名字不是一个 value（因为没有 constructor）。

`Pear` 的 eliminator 的形式如下：

```````````````lisp
(→ Nat Nat
  X) ; X can be any type
```````````````

可以看出，加法（`(→ Nat Nat Nat)`）可以是 `Pear` 的 eliminator。


### `elim-Pear` {#elim-pear}

使用 `define` 没有带来更多的内容，但是可以让代码更加简洁。例如下面的例子：

```````````````lisp
(claim Pear-maker
  U)

(define Pear-maker
  (→ Nat Nat
    Pear))

(claim elim-Pear
  (→ Pear Pear-maker
    Pear))

(define elim-Pear
  (λ (pear maker)
    (maker (car pear) (cdr pear))))

; 如果不用 define 的写法

(claim elim-Pear
  (→ (Pair Nat Nat)
     (→ Nat Nat
       (Pair Nat Nat))
    (Pair Nat Nat)))
```````````````

`elim-Pear` 使得 λ 表达式可以应用于 `Pear`。

```````````````lisp
(elim-Pear
  (cons 3 17)
  (λ (a d)
    (cons d a)))
; (cons 17 3)
```````````````


## Recess: Forkful of Pie {#recess-forkful-of-pie}


### the-expression {#the-expression}

对于 claims 和 definitions，Pie 会返回它们是否是有意义的。对于表达式，Pie 会返回它们的类型和 normal forms。

```````````````lisp
'spinach
; 返回 (the Atom 'spinach)
```````````````

但是 Pie 不一定能自动推断出所有表达式的类型，所以可以用 the-expressions 来告诉 Pie 表达式的类型（类似于 type notations）。例如 Pie 不能自动推断出 `cons` 组成的类型：

```````````````lisp
(the (Pair Atom Atom)
  (cons 'spinach 'cauliflower))

(the
  (Pair Atom
    (Pair Atom Atom))
  (cons 'spinach
    (cons 'kale 'cauliflower))) ; 内层的 cons 不需要另外的 the
```````````````

> **The Law of `the`**
>
> If `X` is a type and `e` is an `X`, then `(the X e)` is an `X`.

<!--quoteend-->

> **The Commandment of `the`**
>
> If `X` is a type and `e` is an `X`, then `(the X e)` is the same `X` as `e`.


### U {#u}

对于 U 这样的类型，它本身就是类型，Pie 会直接返回它的 normal form。

存在一些类型不是 U 的类型，如 `(Pair Atom U)` 等。
