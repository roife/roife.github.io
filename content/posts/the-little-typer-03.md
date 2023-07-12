+++
title = "[The Little Typer] 03 Eliminate All Natural Numbers!"
author = ["roife"]
date = 2021-03-02
series = ["The Little Typer"]
tags = ["Dependent Type", "形式化验证", "Pie", "类型系统", "程序语言理论"]
draft = false
+++

## Total Functions {#total-functions}

全函数就是指“对于任意定义域中的值，都可以给出结果”的函数。

<div class="definition">

**(Total Function)**

A function that always assigns a value to every possible argument is called a total function.

**备注**：Pie 中所有函数都是全函数，而这使得 Pie 中子表达式的求值顺序是无关紧要的。因为如果不是全函数，那么不同的求值顺序会导致函数无值。

</div>


## `iter-Nat` {#iter-nat}

`iter-Nat` 是一个函数，它判断一个 Nat 是否是 `zero`。如果不是，递归迭代 Nat。

使用格式如下：

```lisp
(iter-Nat target
  base
  step)
```

如果 `target is zero`，那么返回 `base`；否则如果是 `(add1 n)`，则返回 `(step (step (... (step zero))))`。`step` 也是一个 λ 表达式。

不过和 `which-Nat` 有一个区别，`iter-Nat` 的 `step` 接受的是一个 `X`（`base` 的返回类型），而 `which-Nat` 接受一个 `Nat`。

`iter-Nat` 也是一个**模式匹配**，但是他可以对自然数进行递归。

> **(The Law of `iter-Nat`)**
>
> If `target` is a `Nat`, `base` is an `X`, and `step` is an `(→ X X)`, then
>
> ```lisp
> (iter-Nat target
>   base
>   step)
> ```
>
> is an `X`.

<!--quoteend-->

> **(The First Commandment of `iter-Nat`)**
>
> If
>
> ````lisp
> (iter-Nat zero
>   base
>   step)
> ````
>
> is an `X`, then it is the same `X` as `base`.

<!--quoteend-->

> **(The Second Commandment of `iter-Nat`)**
>
> If
>
> `````lisp
> (iter-Nat (add1 n)
>   base
>   step)
> `````
>
> is an `X`, then it is the same `X` as
>
> ``````lisp
> (step
>   (iter-Nat n
>     base
>     step))
> ``````
>
> **注解**：为什么前面说 Recursion is not an option，这里又允许迭代呢？是因为这里 `iter-Nat` 的迭代方式是可以确定会 terminate 的，所以加入不影响使用。`iter-Nat` 设定了终值和每次递归的计算方式，最多递归 n 次。


### `+` {#plus}

通过 `iter-Nat` 我们就可以定义加法了：

```````lisp
(claim step-+
  (→ Nat
    Nat))

(define step-+
  (λ (n)
    (add1 n)))

(claim +
  (→ Nat Nat
    Nat))

(define +
  (λ (n j)
    (iter-Nat n
      j
      step-+)))
```````


## `rec-Nat` {#rec-nat}

`rec-Nat` 表示当 `target` 为 `zero` 时，返回 `base`；否则，如果 `target` 是 `(add1 n-1)`，就返回 `(step n-1 step-n-1)`，其中 `step-n-1` 表示下一次递归得到的值。即其展开方式为：

```````lisp
(rec-Nat target
         base
         step)

;; 如果 target 为 n-1 展开后为
(step
 n-1
 (rec-Nat n-1
          base
          step))
```````

`rec-Nat` 结合了 `which-Nat` 和 `iter-Nat` 二者：

-   和 `which-Nat` 的共同点在于 `step` 可以知道当前对于哪一个 Nat 进行递归；
-   和 `iter-Nat` 的共同点在于 `step` 可以进行递归

`rec-Nat` 其实就是 **primitive recursion**。

> **(The Law of `rec-Nat`)**
>
> If `target` is a Nat, `base` is an `X`, and `step` is an
>
> ```````lisp
> (→ Nat X
>   X)
> ```````
>
> then
>
> ````````lisp
> (rec-Nat target
>   base
>   step)
> ````````
>
> is an `X`

<!--quoteend-->

> **(The First Commandment of `rec-Nat`)**
>
> If
>
> `````````lisp
> (rec-Nat zero
>   base
>   step)
> `````````
>
> is an `X`, then it is the same `X` as `base`

<!--quoteend-->

> **(The Second Commandment of `rec-Nat`)**
>
> If
>
> ``````````lisp
> (rec-Nat (add1 n)
>          base
>          step)
> ``````````
>
> is an `X`, then it is the same `X` as
>
> ```````````lisp
> (step n
>   (rec-Nat
>     base
>     step))
> ```````````


### Gauss function 2 {#gauss-function-2}

````````````lisp
(claim step-gauss
  (→ Nat Nat
    Nat)
(define step-gauss
  (λ (n-1 gauss_n-1)
    (+ (add1 n-1) (gauss_n-1 n-1))))

(claim gauss
  (→ Nat
    Nat))
(define gauss
  (λ (n)
    (rec-Nat
      0
      step-gauss)))
````````````


### Multiplication：\* {#multiplication}

````````````lisp
(claim make-step-*
  (→ Nat
     (→ Nat Nat
        Nat)))
(define make-step-*
  (λ (j)
    (λ (n-1 *-n-1)
      (+ j *-n-1))))

(claim *
  (→ Nat Nat
     Nat))
(define *
  (λ (n j)
    (rec-Nat n
      0
      (make-step-* j))))
````````````

这里之所以用 `make-step-*` 是因为这里的 `step` 需要一个额外的参数 `j` 来进行计算。


### Curry {#curry}

其实 `make-step-*` 其实可以直接写成 Curry 的形式，而者在使用上是完全等价的：

````````````lisp
(claim make-step-*
  (→ Nat Nat Nat
    Nat))
(define make-step-*
  (λ (j n-1 *-n-1)
    (+ j *-n-1)))
````````````

`(→ Nat Nat Nat Nat)` 等价于 `(→ Nat (→ Nat (→ Nat Nat)))`，`(f x y z)` 也等价于 `(((f x) y) z)`。

所有的函数实际上只有一个参数。


### factorial 1 {#factorial-1}

````````````lisp
(claim step-xxx
  (→ Nat Nat
    Nat))
(define step-xxx
  (λ (n-1 almost)
    (∗ (add1 n-1) almost)))

(claim xxx
  (→ Nat
    Nat))
(define xxx
  (λ (n)
  (rec-Nat n
    0
    step-xxx)))
````````````

可以发现这个函数永远返回 0，但是实际上我们想要定义一个阶乘函数。问题在于 Nat 这个类型没有明确指出它代表什么数字。
