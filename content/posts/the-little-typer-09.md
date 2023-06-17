+++
title = "[The Little Typer] 09 Double your Money"
author = ["roife"]
date = 2021-03-25
series = ["The Little Typer"]
tags = ["Dependent Type", "形式化验证", "Pie", "类型系统", "程序语言理论"]
draft = false
+++

## `replace` {#replace}

同样是 eliminator，`cong` 的返回值永远是 =-表达式，而 `ind-Nat` 可以借助于 `motive` 返回任何类型。

类似 `ind-Nat` 和 `cong`，有一个类似的 eliminator `replace`。

> **Leibniz's Law**
>
> 1.  If two expressions are equal, then whatever is true for one is true for the other.
> 2.  if whatever is true for one is true for the other, then they are equal.

`replace` 中的 motive 表示变换规则，`base` 表示 `(motive from)` 成立的 evidence，返回值为 `(motive to)`。

即传入 `(= A B)` 与 `(f A)`，返回 `(f B)`。

> **The Law of `replace`**
>
> If `target` is an `(= X from to)`, `mot` is an `(→ X U)` and `base` is a `(mot from)`, then
>
> ```lisp
> (replace target
>   mot
>   base)
> ```
>
> is a `(mot to)`.
>
> **注解**：类似于 Coq 的 `rewrite -> target`


## `incr=add1`: `replace` {#incr-add1-replace}

这里使用 `replace` 表达式改写 `step-incr=add1`。

````lisp
(claim step-incr=add1
       (Π ((n-1 Nat))
          (→ (= Nat       ; incr=add1_n-1 (base)
                (incr n-1) ; from_n-1
                (add1 n-1)) ; to_n-1
             (= Nat ; (mot to_n-1): the value for replace
                (incr (add1 n-1))
                (add1 (add1 n-1))))))

(define step-incr=add1
    (λ (n-1)
       (λ (incr=add1_n-1)
          (replace incr=add1_n-1
                   ;; motive
                   ;; base
                   ))))
````


### motive for `replace` {#motive-for-replace}

首先要确定 `replace` 表达式中 motive 的写法。

`target` 的类型为 `(= Nat (incr n-1) (add1 n-1))`；其中 `to` 的类型为 `(add1 n-1)`。

`replace` 的结果类型为 `(mot (add1 n-1))`，即：

````lisp
(= Nat
   (add1 (incr n-1))
   (add1 [(add1 n-1)])) ;; [] 内为 to 的部分
````

`[]` 内的部分可以作为参数，写成一个 λ 表达式：

````lisp
(λ (k)
  (= Nat
    (add1 (incr n-1))
    (add1 k)))
````

将 `target` 的 `base` 部分（`incr n-1`）代入得到一个显然成立的式子：

````lisp
(= Nat
  (add1
    (incr n-1))
  (add1
    (incr n-1)))
; => (same (add1 incr n-1))
````

因此可以得到 motive。

这里 motive 有两个参数，第一个是递推时当前递推到的步骤，即主动传入的 `n-1`；第二个，由 `replace` 自动应用。

````lisp
(claim mot-step-incr=add1
  (→ Nat Nat
    U))

(define mot-step-incr=add1
  (λ (n-1 k)
    (= Nat
      (add1 (incr n-1))
      (add1 k))))
````


### step in `replace` {#step-in-replace}

````lisp
(define step-incr=add1
  (λ (n-1)
    (λ (incr=add1_n-1)
      (replace incr=add1_n-1
        (mot-step-incr=add1 n-1)
        (same (add1 (incr n-1)))))))
````


## `double` &amp; `twice` {#double-and-twice}

-   `(double n)`：`(+ 2 (+ 2 ...))`
-   `(twice n)`：`(+ n n)`

<!--listend-->

````lisp
(claim double
  (→ Nat
    Nat))

(define double
  (λ (n)
    (iter-Nat n
      0
      (+ 2))))
````

````lisp
(claim twice
  (→ Nat
    Nat))

(define twice
  (λ (n)
    (+ n n)))
````

下面要证明二者是相同的。


### `add1+=+add1` {#add1-plus-plus-add1}

前面已经证明了第一个加数的 `add1` 可以挪到 `+` 的外面（由 `ind-Nat` 显然），所以现在要证明的是第二个加数的 `add1` 可以挪到第一个加数上。即：`(+ (add1 n) (add1 m))` \\(\rightarrow\\) `(+ (add1 (add1 n)) m)` \\(\rightarrow\\) `(add1 (add1 (+ n m)))`。

所以要先证明 `(+ n (add1 j))` 与 `(add1 (+ n j))` 相同。

````lisp
(claim add1+=+add1
  (Π ((n Nat)
      (j Nat))
    (= Nat
      (add1 (+ n j))
      (+ n (add1 j)))))

(define add1+=+add1
  (λ (n j)
    (ind-Nat n
      (mot-add1+=+add1 j)
      (same (add1 j))
      (step-add1+=+add1 j))))

(claim mot-add1+=+add1
  (→ Nat Nat
    U))

(define mot-add1+=+add1
  (λ (j k)
    (= Nat
      (add1 (+ k j))
      (+ k (add1 j)))))
````


#### `step` {#step}

首先观察 `mot-add1+=+add1` 的结果：

````lisp
; (mot-add1+=+add1 j n-1)
(= Nat
  (add1 (+ n-1 j))
  (+ n-1 (add1 j)))

; (mot-add1+=+add1 j (add1 n-1))
(= Nat
  (add1 (+ (add1 n-1) j))
  (+ (add1 n-1) (add1 j)))

; 由于 + 是 ind-Nat 定义的，所以对 target 可以展开一层 step，就可以发现和前者的关系了
(= Nat
  (add1 (add1 (+ n-1 j)))
  (add1 (+ n-1 (add1 j))))
````

显然只要在外面加一层 `add1`。

````lisp
(claim step-add1+=+add1
  (Π ((j Nat)
      (n-1 Nat))
    (→ (mot-add1+=+add1 j
        n-1)
      (mot-add1+=+add1 j
        (add1 n-1)))))

(define step-add1+=+add1
  (λ (j n-1)
    (λ (add1+=+add1_n-1)
      (cong add1+=+add1_n-1
        (+ 1)))))
````


### `twice=double` {#twice-double}

````lisp
(claim twice=double
  (Π ((n Nat))
    (= Nat (twice n) (double n))))

(define twice=double
  (λ (n)
    (ind-Nat n
      mot-twice=double
      (same zero)
      step-twice=double)))

(claim mot-twice=double
  (→ Nat
    U))

(define mot-twice=double
  (λ (k)
    (= Nat
      (twice k)
      (double k))))

(claim step-twice=double
  (Π ((n-1 Nat))
    (→ (mot-twice=double n-1)
       (mot-twice=double (add1 n-1)))))
````

> **Observation about +**
>
> No matter which Nats `j` and `k` are, `(+ (add1 j) k)` is the same Nat as `(add1 (+ j k))`.

即 `step` 返回值的类型为：

````lisp
(= Nat
  (add1
    (+ n-1 (add1 n-1)))
  (add1
    (add1 (double n-1))))
````

考虑 `(cong twice=double_n-1 (+ 2))` 为：

````lisp
(= Nat
  (add1
    (add1 (+ n-1 n-1))) ; 需要 replace
  (add1
    (add1 (double n-1))))
````

所以要把 `(add1 (add1 (+ n-1 n-1)))` 替换成 `(add1 (+ n-1 (add1 n-1)))`。

<!--list-separator-->

-  使用 replace

    ````lisp
    (claim mot-step-twice=double
      (→ Nat Nat
        U))

    (define mot-step-twice=double
      (λ (n-1 k)
        (= Nat
          (add1
            k)
          (add1
            (add1 (double n-1))))))
    ````

    由此得到了 `step-twice=double`：

    ````lisp
    (define step-twice=double
      (λ (n-1)
        (λ (twice=double_n-1)
          (replace (add1+=+add1 n-1 n-1)
            (mot-step-twice=double n-1)
            (cong twice=double_n-1
              (+ 2))))))
    ````

    解释一下 `replace` 的部分：

    target 的 `from` 为 `(add1 (+ n-1 n-1))`，`to` 为 `(+ n-1 (add1 n-1))`。

    `(mot from)` 为：

    ````lisp
    (= Nat
      (add1
        (add1 (+ n-1 n-1))) ; k 被替换
      (add1
        (add1 (double n-1))))
    ````

    `(mot to)` 为：

    ````lisp
    (= Nat
      (add1
        (+ n-1 (add1 n-1))) ; k 被替换
      (add1
        (add1 (double n-1))))
    ````

    真正的 `step` 是 `(cong twice=double_n-1 (+ 2))`，得到答案后用 `replace` 进行代换。


## `twice-Vec` &amp; `double-Vec` {#twice-vec-and-double-vec}

`twice-Vec` 和 `double-Vec` 用于复制列表元素，即将 `['a 'b]` 变为 `['a 'a 'b 'b]`，区别是类型定义用的是 `twice` 还是 `double`。

````lisp
(claim twice-Vec
  (Π ((E U)
      (l Nat))
    (→ (Vec E l)
      (Vec E (twice l)))))
````

但是归纳定义 `twice-Vec` 十分困难，因为 `(twice (add1 n-1))` 为 `(add1 (+ n-1 (add1 n-1)))`。要用 `vec::` 拼接列表时，必须要长度加一，即在顶部添加一个 `add1`。但是 `twice-Vec` 只有一个 `add1` 在顶部可以被添加。

相比而言由于 `(double (add1 n-1))` 为 `(add1 (add1 (double n-1)))`，所以归纳起来比较容易，所以先定义 `double-Vec`。


### `double-Vec` {#double-vec}

````lisp
(claim double-Vec
  (Π ((E U)
      (l Nat))
    (→ (Vec E l)
      (Vec E (double l)))))

(claim base-double-Vec
  (Π ((E U))
    (→ (Vec E zero)
      (Vec E (double zero)))))

(define base-double-Vec
  (λ (E)
    (λ (es)
      vecnil)))

(claim mot-double-Vec
  (→ U Nat
    U))

(define mot-double-Vec
  (λ (E k)
    (→ (Vec E k)
      (Vec E (double k)))))

(claim step-double-Vec
  (Π ((E U)
      (l-1 Nat))
    (→ (→ (Vec E l-1)
        (Vec E (double l-1)))
      (→ (Vec E (add1 l-1))
        (Vec E
          (double (add1 l-1)))))))

(define step-double-Vec
  (λ (E l-1)
    (λ (double-Vec_l-1)
      (λ (es)
        (vec:: (head es)
          (vec:: (head es)
            (double-Vec_l-1
              (tail es))))))))

(define double-Vec
  (λ (E l)
    (ind-Nat l
      (mot-double-Vec E)
      (base-double-Vec E)
      (step-double-Vec E))))
````


### `twice-Vec` {#twice-vec}

在定义了 `double-Vec` 后，再利用 `double-Vec` 定义 `twice-Vec`。

由于 `(twice=double l)` 为 `(` Nat (twice l) (double l))=，其 `from` 和 `to` 和我们要的相反了，所以可以用 `symm` 来颠倒等号的两边。

````lisp
(define twice-Vec
  (λ (E l)
    (λ (es)
      (replace (symm
                (twice=double l))
        (λ (k)
          (Vec E k))
        (double-Vec E l es)))))
````


#### `symm` {#symm}

`symm` 可以用来交换 `=` 的两边。

> **The Law of `symm`**
>
> If `e` is an `(= X from to)`, then `(symm e)` is an `(= X to from)`.

<!--quoteend-->

> **The Commandment of `symm`**
>
> If `x` is an `X`, then `(symm (same x))` is the same `(= X x x)` as `(same x)`.
