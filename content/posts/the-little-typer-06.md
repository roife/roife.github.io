+++
title = "[The Little Typer] 06 Precisely How Many?"
author = ["roife"]
date = 2021-03-20
series = ["The Little Typer"]
tags = ["Dependent Type", "形式化验证", "Pie", "类型系统", "程序语言理论"]
draft = false
+++

## `head` &amp; `last` {#head-and-last}

-   `(head es)`：取列表的第一个元素
-   `(last es)`：取列表的最后一个元素

可以看出 `head` 不是一个 total function，因为它不能对 `nil` 使用。


## Vec {#vec}

`(Vec E k)` 表示一个长度为 `k` 的 `(List E)`：

-   `(Vec E zero)` 的 constructor 为 `vecnil`
-   `(Vec E (add1 k))` 的 constructor `vec::`
-   当 `e` 为 `E` 类型，而且 `es` 为 `(Vec E k)` 类型时，`(vec:: e es)` 的类型为 `(Vec E (add1 k))`
-   如果一个表达式的类型为 `(Vec E (add1 k))`，则这个列表一定至少有一个 entry

> **The Law of `Vec`**
>
> If `E` is a type and `k` is a Nat, then `(Vec E k)` is a type.

<!--quoteend-->

> **The Law of `vecnil`**
>
> `vecnil` is a `(Vec E zero)`.

<!--quoteend-->

> **The Law of `vec::`**
>
> If `e` is an `E` and `es` is a `(Vec E k)`, then `(vec:: e es)` is a `(Vec E (add1 k))`.


### `head` 与 `tail` {#head-与-tail}

-   `(head es)` is an `E` when `es` is a `(Vec E (add1 k))`
-   `(tail es)` is a `(Vec E k)` when `es` is a `(Vec E (add1 k))`


### `first-of-one` {#first-of-one}

-   `(find-of-one E es)`：在只有一个元素的列表中寻找

<!--listend-->

```lisp
(claim first-of-one
  (Π ((E U))
    (→ (Vec E 1)
      E)))

(define first-of-one
  (λ (E)
    (λ (es)
      (head es))))
```

`find-of-one` 的类型定义中指定传入元素必须是 `(Vec E 1)`，所以不符合要求的参数都会被拒绝。


## Π 表达式 {#π-表达式}

同理还可以定义 `first-of-two`、`first-of-three` 等。我们想用 Π 表达式定义一个应用更广泛的 `first`（即 typed-head）。

```lisp
(claim first
  (Π ((E U)
      (l Nat)) ; 定义了一个用于类型定义的 Nat
  (→ (Vec E (add1 l)) ; 长度至少为 1
    E)))

(define first
  (λ (E l)
    (λ (es)
      (head es))))
```

> **The Law of Π**
>
> The expression
>
> ```lisp
> (Π ((y Y))
>   X)
> ```
>
> is a type when `Y` is a type, and `X` is a type if `y` is a `Y`.

我们通过一个更加具体的类型（即那个 `Nat` 参数）规范了传入的参数。


### → 表达式与 Π 表达式 {#表达式与-π-表达式}

<div class="definition">

**(→ and Π)**

The type

````java
(→ Y
  X)
````

is a shorter way of writing

````java
(Π ((y Y))
  X)
````

when `y` is not used in `X`.

**注解**：实际 → 表达式是 Π 表达式的特殊形式，传入类型参数和传入值参数没有区别。使用 Π 传入的参数可以被后面的类型所依赖（类似 `let*`），使用 → 传入的参数则不能依赖（类似 `let`）。

</div>

例如 `first` 也可以写成这样：

````lisp
(claim first
  (Π ((E U)
      (l Nat)
      (es (Vec E (add1 l))))
    E))
````

> **The Final Law of λ**
>
> If `x` is an `X` when `y` is a `Y`, then
>
> ````lisp
> (λ (y)
>   x)
> ````
>
> is a
>
> `````lisp
> (Π ((y Y))
>   X)
> `````

<!--quoteend-->

> **The Final Law of Application**
>
> If `f` is a
>
> ``````lisp
> (Π ((y Y))
>   X)
> ``````
>
> and `z` is a `Y`, then
>
> ```````lisp
> (f z)
> ```````
>
> is an `X`, where every `y` has been consistently replaced by `z`.

<!--quoteend-->

> **The Final First Commandment of λ**
>
> If two λ-expressions can be made the same
>
> ````````lisp
> (Π ((y Y))
>   X)
> ````````
>
> by consistently renaming their variables, then they are the same.

<!--quoteend-->

> **The Final Second Commandment of λ**
>
> If `f` is a
>
> `````````lisp
> (Π ((y Y))
>   X)
> `````````
>
> and `y` does not occur in `f` , then `f` is the same as
>
> ``````````lisp
> (λ (y)
>   (f y))
> ``````````


### `rest` {#rest}

`rest` 即 typed-tail。

```````````lisp
(claim rest
  (Π ((E U)
      (l Nat))
    (→ (Vec E (add1 l))
      (Vec E l))))

(define rest
  (λ (E l)
    (λ (es)
      (tail es))))
```````````
