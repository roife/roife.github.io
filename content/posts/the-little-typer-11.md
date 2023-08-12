+++
title = "[The Little Typer] 11 All lists are created equals"
author = ["roife"]
date = 2021-03-30
series = ["The Little Typer"]
tags = ["Dependent Type", "形式化验证", "Pie", "类型系统", "程序语言理论"]
draft = false
+++

## `ind-Vec` {#ind-vec}

一个 `ind-Vec` 表达式为：

```lisp
(ind-Vec n es
  mot
  base
  step)
```

相比于 `ind-List=，=ind-Vec` 的每个参数都多了一个 Nat `k` 表示数量。

`mot` 的类型为：

```lisp
(Π ((k Nat))
  (→ (Vec E k)
    U))
```

可以发现 `mot` 的参数中没有 `E` 而有 `k=。因为对于一个 =Vec=，=E` 是确定不变的，而 `k` 会改变（例如 `step` 调用 motive 推导类型时，每次的 `n` 都会改变）。确定不变的称为 parameters，而有可能会改变的称为 indices。这里没出现的 parameter 用 curry-ing 的方法传入。

> A family of types whose argument is an index is sometimes called “an indexed family.

`base` 的类型为 `(mot zero vecnil)=，=step` 的类型为：

```lisp
(Π ((k Nat)
    (h E)
    (t (Vec E k)))
  (→ (mot k t)
    (mot (add1 k) (vec:: h t))))
```

> **The Law of `ind-Vec`**
>
> If `n` is a Nat, `target` is a `(VecE n)`, `mot` is a
>
> ```lisp
> (Π ((k Nat))
>   (→ (Vec E k)
>     U))
> ```
>
> `base` is a `(mot zero vecnil)`, and `step` is a
>
> ````lisp
> (Π ((k Nat)
>     (h E)
>     (t (Vec E k)))
>   (→ (mot k t)
>     (mot (add1 k) (vec:: h t))))
> ````
>
> then
>
> `````lisp
> (ind-Vec n target
>   mot
>   base
>   step)
> `````
>
> is a `(mot n target)`

`ind-Vec` 中的 motive 接受两个参数。注意这和前面的 motive 不一样，前面的 motive 虽然也是接受两个参数，但是其中一个会通过 curry-ing 提前传入，所以实际上只有一个参数。

> **The First Commandment of `ind-Vec`**
>
> The ind-Vec-expression
>
> ``````lisp
> (ind-Vec zero vecnil
>   mot
>   base
>   step)
> ``````
>
> is the same `(mot zero vecnil)` as `base`.

<!--quoteend-->

> **The Second Commandment of `ind-Vec`**
>
> The ind-Vec-expression
>
> ```````lisp
> (ind-Vec (add1 n) (vec:: e es)
>   mot
>   base
>   step)
> ```````
>
> is the same `(mot (add1 n) (vec:: e es))` as
>
> ````````lisp
> (step n e es
>   (ind-Vec n es
>     mot
>     base
>     step))
> ````````


## `vec-append` {#vec-append}

-   =(vec-append E l j v1 v2)=：合并两个 Vec

<!--listend-->

`````````lisp
(claim vec-append
  (Π ((E U)
      (l Nat)
      (j Nat))
    (→ (Vec E l) (Vec E j)
       (Vec E (+ l j)))))

(define vec-append
  (λ (E l j)
    (λ (es end)
      (ind-Vec l es
        (mot-vec-append E j)
        end
        (step-vec-append E j)))))
`````````


### motive {#motive}

`````````lisp
(claim mot-vec-append
  (Π ((E U)
      (j Nat)
      (k Nat))
    (→ (Vec E k)
       U)))

(define mot-vec-append
  (λ (E j k)
    (λ (es)
      (Vec E (+ j k)))))
`````````

这里 motive 先传入 `end` 的长度 `j` 再传入剩余列表长度 `k=，是因为前者在 =claim` 里面要用到，由于 `j` 每次是不变的，所以可以直接通过 curry-ing 传入。否则就要写成下面的形式来交换参数：

`````````lisp
(claim mot-vec-append
  (Π ((E U)
      (k Nat)
      (j Nat))
    (→ (Vec E j)
       U)))

(define vec-append
  (λ (E l j es end)
    (ind-Vec l es
      (λ (k)
        (mot-vec-append E k j))
        end
        step-vec-append )))
`````````


### `step` {#step}

`````````lisp
(claim step-vec-append
  (Π ((E U)
      (j Nat)
      (k Nat)
      (e E)
      (es (Vec E k)))
    (→ (mot-vec-append E j k es)
      (mot-vec-append E j (add1 k) (vec:: e es)))))

(define step-vec-append
  (λ (E j l-1 e es) ; es 是当前拆分的列表
    (λ (vec-append_es) ; vec-append_es 是递归返回的结果
      (vec:: e vec-append_es))))
`````````


## Extrinsic Proof for `list→vec` {#extrinsic-proof-for-list-vec}

用一个 specific 的类型相当于将证明用类型来实现，所以称为 instrinsic proof。反之，用一个额外的证明则称为 extrinsic proof。

例如对于 `list→vec` 的一个证明是将 List 变为 Vec，然后变回 List 仍然是同样的列表。因此，这需要定义 =vec→list=。


### `vec→list` {#vec-list}

`````````lisp
(claim vec→list
  (Π ((E U)
      (l Nat))
    (→ (Vec E l)
       (List E))))

(claim mot-vec→list
  (Π ((E U)
      (l Nat))
    (→ (Vec E l)
       U)))

(define mot-vec→list
  (λ (E l)
    (λ (es)
      (List E))))

(claim step-vec→list
  (Π ((E U)
      (l Nat)
      (e E)
      (es (Vec E l)))
    (→ (List E)
       (List E))))

(define step-vec→list
  (λ (E l e es)
    (λ (vec→list_es)
      (:: e vec→list_es))))

(define vec→list
  (λ (E l)
    (λ (es)
      (ind-Vec l es
        (mot-vec→list E)
        nil
        (step-vec→list E)))))
`````````


### `list→vec→list=` {#list-vec-list}

`````````lisp
(claim list→vec→list=
  (Π ((E U)
      (es (List E)))
    (= (List E)
       es
       (vec→list E (length E es)
         (list→vec E es)))))

(claim mot-list→vec→list=
  (Π ((E U))
    (→ (List E)
       U)))

(define mot-list→vec→list=
  (λ (E)
    (λ (es)
      (= (List E)
        es
        (vec→list E (length E es)
          (list→vec E es))))))

(claim step-list→vec→list=
  (Π ((E U)
      (e E)
      (es (List E)))
    (→ (mot-list→vec→list= E es)
       (mot-list→vec→list= E (:: e es)))))

(claim ::-fun
  (Π ((E U))
    (→ E (List E) (List E))))

(define ::-fun
  (λ (E)
    (λ (e es)
      (:: e es))))

(define step-list→vec→list=
  (λ (E e es)
    (λ (list→vec→list=_es)
      (cong list→vec→list=_es
        (::-fun E e)))))

(define list→vec→list=
  (λ (E es)
    (ind-List es
      (mot-list→vec→list= E)
      (same nil)
      (step-list→vec→list= E))))
`````````

这里的 `step` 比较特殊：

step 要把

`````````lisp
(= (List E)
  es
  (vec→list E (length E es)
    (list→vec E es)))
`````````

变成

`````````lisp
(= (List E)
  (:: e es)
  (vec→list E (length E (:: e es))
    (list→vec E (:: e es))))
`````````

即

`````````lisp
(= (List E)
  (:: e es)
  (vec→list E (add1 (length E es))
    (vec:: e (list→vec E es))))
`````````

再求值一次得到：

`````````lisp
(= (List E)
  (:: e es)
  (::e
    (vec→list E (length E es)
      (list→vec E es))))
`````````

所以只要用一次 `cong` 就好了。

> **When in Doubt, Evaluate**
>
> Gain insight by finding the values of expressions in types and working out examples in "same-as" charts.


### `length-treats=` {#length-treats}

两个相同的列表具有相同的长度：

`````````lisp
(claim length-treats=
  (Π ((some-treats (List Atom))
      (more-treats (List Atom)))
    (→ (= (List Atom)
          some-treats
          more-treats)
      (= Nat
        (length Atom some-treats)
        (length Atom more-treats)))))

(define length-treats=
  (λ (some-treats more-treats)
    (λ (treats=)
      (cong treats= (length Atom)))))
`````````
