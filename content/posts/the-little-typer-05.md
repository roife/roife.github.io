+++
title = "[The Little Typer] 05 Lists, Lists, and More Lists"
author = ["roife"]
date = 2021-03-09
series = ["The Little Typer"]
tags = ["Dependent Type", "形式化验证", "Pie", "类型系统", "程序语言理论"]
draft = false
+++

## List {#list}

列表的类型是 `(List E)`，其中 `List` 是一个 type constructor。它有两个 constructor，分别是 `nil` 与 `::`。

可以发现，`List` 和 `Nat` 很像，`nil` 对应 `zero`，`::` 对应 `add1`。

> **The Law of List**
>
> if `E` is a type, then `(List E)` is a type.

<!--quoteend-->

> **The Law of `nil`**
>
> `nil` is a `(List E)`, no matter what type `E` is.

<!--quoteend-->

> **The Law of `::`**
>
> If `e` is an `E` and `es` is a `(ListE)`, then `(:: e es)` is a `(List E)`.


## `rec-List` {#rec-list}

类似 `rec-Nat`，有 `rec-List`。`(step e es step-n-1)` 的三个参数分别代表 `car`、`cdr`、下一层递归的返回值。

> **The Law of `rec-List`**
>
> If target is a `(List E)`, `base` is an `X`, and `step` is an
>
> ```lisp
> (→ E (List E) X
>   X)
> ```
>
> then
>
> ````lisp
> (rec-List target
>   base
>   step)
> ````
>
> is an `X`.

<!--quoteend-->

> **The First Commandment of `rec-List`**
>
> If
>
> `````lisp
> (rec-List nil
>   base
>   step)
> `````
>
> is an `X`, then it is the same `X` as `base`.

<!--quoteend-->

> **The Second Commandment of `rec-List`**
>
> If
>
> ``````lisp
> (rec-List (:: e es)
>   base
>   step)
> ``````
>
> is an `X`, then it is the same `X` as
>
> ```````lisp
> (step e es
>   (rec-List es
>     base
>     step))
> ```````


### `length` {#length}

````````lisp
(claim step-length
  (Π ((E U))
    (→ E (List E) Nat
      Nat)))

(define step-length
  (λ (E)
    (λ (e es length_es)
      (add1 length_es))))

(claim length
  (Π ((E U))
    (→ (List E)
       Nat)))

(define length
  (λ (E)
    (λ (es)
      (rec-List es
        0
        (step-length E)))))
````````


### `append` {#append}

在一个列表后面添加另一个列表。

````````lisp
(claim step-append
  (Π ((E U))
    (→ E (List E) (List E)
      (List E))))

(define step-append
  (λ (E)
    (λ (e es append_es)
      (:: e append_es))))

(claim append
  (Π ((E U))
    (→ (List E) (List E)
      (List E))))

(define append
  (λ (E)
    (λ (start end)
      (rec-List start
        end
        (step-append E)))))
````````

可以发现，`append` 和 `+` 非常像。


### `snoc` {#snoc}

在列表末尾添加元素。

````````lisp
(claim snoc
  (Π ((E U))
    (→ (List E) E
      (List E))))

(define snoc
  (λ (E)
    (λ (start e)
      (rec-List start
        (:: e nil)
        (step-append E)))))
````````


### `concat` {#concat}

类似于 `append`，使用 `snoc` 定义。

````````lisp
(claim step-concat
  (Π ((E U))
    (→ E (List E) (List E)
      (List E))))

(define step-concat
  (λ (E)
    (λ (e es concat_es)
      (snoc E concat_es e))))

(claim concat
  (Π ((E U))
    (→ (List E) (List E)
      (List E))))

(define concat (λ (E)
  (λ (start end)
    (rec-List end
      start
      (step-concat E)))))
````````


### `reverse` {#reverse}

翻转一个列表。

````````lisp
(define step-reverse
  (λ (E)
    (λ (e es reverse_es)
      (snoc E reverse_es e))))

(define reverse
  (λ (E)
  (λ (es) (rec-List es
    nil
    (step-reverse E)))))
````````
