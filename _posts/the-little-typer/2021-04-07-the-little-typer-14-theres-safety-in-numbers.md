---
layout: "post"
title: "「The Little Typer」 14 There's Safety in Numbers"
subtitle: "Maybe, Fin, Trivial & Absurd, Turner’s Teaser"
author: "roife"
date: 2021-04-07

tags: ["The Little Typer@读书笔记", "读书笔记@Tags", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "Pie@编程语言", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

从一个 List 中取出某个位置的元素时，可能会发生对应的位置不存在值的情况，这个时候函数不是 total 的。前面已经用 `Vec` 来使得函数是 total 的。下面继续用两种方法构建一个 total 的函数。

# `list-ref`

## `Trivial`: Unit Type

`Trivial Type`，也叫 `Unit Type`，只有一个 constructor `sole`，并且不能嵌套其他表达式或者递归定义。

> **The Law of `Trivial`**
>
> `Trivial` is a type.

> **The Law of `sole`**
>
> `sole` is a `Trivial`.

> **The Commandment of `sole`**
>
> If `e` is a `Trivial`, then `e` is the same as `sole`.

## `Maybe`

`Maybe` 可以表示一个值，或者不存在值。

```lisp
(claim Maybe
  (→ U
    U))

(define Maybe
  (λ (X)
    (Either X Trivial)))
```

下面定义 Maybe Monad。

`nothing` 表示不存在值，即返回一个 `Trivial`；反之，则用 `just` 表示存在值。

```lisp
(claim nothing
  (Π ((E U))
    (Maybe E)))

(define nothing
  (λ (E)
    (right sole)))

(claim just
  (Π ((E U))
    (→ E
      (Maybe E))))

(define just
  (λ (E e)
    (left e)))
```

### `maybe-head`

用 `Maybe` 可以写出一个 total 的 `maybe-head`。

返回值为 `(nothing Type)` 或者 `(just Type Value)`。

```lisp
(claim maybe-head
  (Π ((E U))
    (→ (List E)
      (Maybe E))))

(define maybe-head
  (λ (E es)
    (rec-List es
      (nothing E) ; 不存在值
      (λ (hd tl head_tl) ; 存在值
        (just E head_tl)))))
```

### `maybe-tail`

```lisp
(claim maybe-tail
  (Π ((E U))
    (→ (List E)
      (Maybe (List E)))))

(define maybe-tail
  (λ (E es)
    (rec-List es
      (nothing (List E))
      (λ (hd tl tail_tl)
        (just (List E) tl)))))
```

### `list-ref`

- `(list-ref E Nat (List E))`：传入一个 Nat 和列表，返回列表中对应位置的元素（索引从 0 开始）

```lisp
(claim list-ref
  (Π ((E U))
    (→ Nat (List E)
      (Maybe E))))

(claim step-list-ref
  (Π ((E U))
    (→ Nat
       (→ (List E)
         (Maybe E))
      (→ (List E)
        (Maybe E)))))

(define step-list-ref
  (λ (E)
    (λ (n-1 list-ref_n-1)
      (λ (es)
        (ind-Either (maybe-tail E es)
          (λ (maybe_tl)
            (Maybe E))
          (λ (tl)
            (list-ref_n-1 tl))
          (λ (empty)
            (nothing E)))))))

(define list-ref
  (λ (E n)
  (rec-Nat n
    (maybe-head E) ; (→ (List E) (Maybe E))
    (step-list-ref E))))
```

# `vec-ref`

显然，这种有约束条件的函数，为了使其成为 total function，也可以用 `Vec` 来写。

## `Absurd`: Empty Type

类似于 `Trivial`，`Absurd` 也是一个类型。`Absurd` 也叫做 `Emtpy Type` 或者 `Bottom Type`。

> **The Law of `Absurd`**
>
> `Absurd` is a type.

和 `Trivial` 不同的是，`Absurd` 没有 constructor，也没有 value，但是存在 `Absrud` 的表达式（neutral expressions）。

所有 `Absurd` 的表达式都是相同（same）的。

> **The Commandment of Absurdities**
>
> Every expression of type `Absurd` is neutral, and all of them are the same.

```lisp
// 一个 Absurd 的例子
(claim similarly-absurd
  (→ Absurd
    Absurd))

(define similarly-absurd
  (λ (x)
    x))
```

## `ind-Absurd`

虽然 `Absurd` 没有 constructor，但是有一个 eliminator：`ind-Absurd`。

之前都将 eliminators 看作一种提取信息的方法，而这里将其看作一种可以对于某种类型的所有值得出新表达式的方法（例如 `length` 对于 `List` 得出一个 `Nat`）。而 eliminator 的类型由 motive 决定。

所以虽然 `Absurd` 没有 values，但是 `ind-Absurd` 通过 motive 可以得出新的值。同样，`ind-Absurd` 没有 `base` 和 `step`（因为没有值）。其格式为：

```lisp
(ind-Absurd target
  mot)
```

其中 `mot` 不是 Π 表达式（函数），而是一个 `U`（类型）。（因为 `Absurd` 没有值，所以也没有 target 可以传入）

> **The Law of `ind-Absurd` The expression**
>
> ```lisp
> (ind-Absurd target
>   mot)
> ```
>
> is a `mot` if `target` is an `Absurd` and `mot` is a `U`.
>
> **注解**：即 `ind-Absurd` 可以推出**任何类型**。
>
> 构建证明时，某个地方的条件为 `Absurd`，则此时命题一定成立（假命题可以推出任何命题）。那么此时利用 `ind-Absurd` 令 `mot` 为目标命题，相当于直接从 `Absurd` 推出了目标命题，填补了证明。

通过 `ind-Absurd`，可以表达“某个表达式永远无法被 evaluate”，即其是 permanently neutral expressions。

## `Fin`

为了能够定义一个这样的符合条件函数，需要表达“传入的参数必须小于 Vec 的长度”这个概念。这里用新的类型 `Fin` 来表达。其定义为 `(Fin l)`，其中 `l` 表示长度。

- `(Fin 0)` 表示小于 0，由于这样的 Nat 是不存在的（should have 0 values），所以它的类型为 `Absurd`。即 `Fin` 的 `base` 为 `Absurd`
- `(Fin 1)` 表示小于 1，由于这样的 Nat 只有一个（即 `0`），它的类型为 `(Maybe Absurd)`。此时它只能是 `(nothing Absurd)`，即 `(right sole)`。（不能是 `(just Absurd)`，因为 `Absurd` 没有 values）
- `(Fin 2)` 的类型应该是 `(Maybe (Maybe Absurd))`，其两个值分别为 `(nothing (Maybe Absurd))` 和 `(just (Maybe Absurd) (nothing Absurd))`，即 `(right sole)` 和 `(left (right sole))`
- `(Fin 3)` 的类型是 `(Maybe (Maybe (Maybe Absurd)))` 有三个元素：`(right sole)`、`(left (right sole))`、`(left (left (right sole)))`
- 可以看出 `nothing`/`left` 有点像 `add1`，`just`/`(right sole)` 有点像 `zero`

由此可以推广到如果 `X` 有 `n` 个 values，那么 `(Maybe X)` 有 `(add1 n)` 个 values（有点像左偏树），分别是：
- `(just X)`：共 `n` 种
- `(nothing X)`：共一种

所以可以用 `Maybe` 作为 `Fin` 的 `step`。

```lisp
(claim Fin
  (→ Nat
    U))

(define Fin
  (λ (n)
    (iter-Nat n
      Absurd
      Maybe)))
; (Fin 1) => (Either Absurd Trivial)
; (Fin 2) => (Either (Either Absurd Trivial) Trivial)
```

### `fzero` & `fadd1`

如果一个值的类型为 `(Fin n)`，那么它可以是 `0, 1, ..., n-1`，但是不可以大于等于 `n`。其具体的值可以用 `fzero` 和 `fadd1` 构建（这两个类似于 constructor）。

- `(fzero n)`：构建 `(Fin (add1 n))` 下的 0（因为 `(Fin n)` 指的是小于 `n` 的值，所以没有 `(fzero 0)`，至少为 `(fzero 1)`）

```lisp
(claim fzero
  (Π ((n Nat))
    (Fin (add1 n))))
; 也可以展开写成
; (Π ((n Nat))
;   (Maybe (Fin n)))

(define fzero
  (λ (n)
    (nothing (Fin n))))
; (fzero 0) =>
;   (the (Either Absurd Trivial)
;     (right sole))
;
; (fzero 1) =>
;   (the (Either (Either Absurd Trivial)
;     Trivial)
;       (right sole))
```

- `(fadd1 n (Fin n))`：传入一个 `(Fin n)` 的值，构建 `(Fin (add1 n))` 类型下的 `(add1 n)`

```lisp
(claim fadd1
  (Π ((n Nat))
    (→ (Fin n)
      (Fin (add1 n)))))

(define fadd1
  (λ (n)
    (λ (i-1)
      (just (Fin n) i-1))))
```

## `vec-ref`

- `(vec-ref E l i es)`：在长度为 `l` 的 Vec `es` 中找到第 `i` 个位置的元素（`i` 为 `(Fin l)`）

```lisp
(claim vec-ref
  (Π ((E U)
      (l Nat))
    (→ (Fin l) (Vec E l)
      E)))
```

此时对于 `l` 和 `(Fin l)` 有三种情况：
- `l` 为 `zero`
- `l` 有 `add1`，`(Fin l)` 为 `fzero`
- `l` 有 `add1`，`(Fin l)` 有 `fadd1`

这里的 `vec-ref` 返回值是一个可以被 curry-ing 的函数。

```lisp
(claim base-vec-ref ; apply zero to the motive
  (Π ((E U))
    (→ (Fin zero) (Vec E zero)
      E)))

(define base-vec-ref
  (λ (E)
    (λ (no-value-ever es)
      (ind-Absurd no-value-ever
        E))))

(claim step-vec-ref
  (Π ((E U)
      (l-1 Nat))
    (→ (→ (Fin l-1)
          (Vec E l-1)
        E) ; (mot-vec-ref l-1)
      (→ (Fin (add1 l-1))
         (Vec E (add1 l-1))
        E)))) ; (mot-vec-ref (add1 l-1))

(define step-vec-ref
  (λ (E l-1)
    (λ (vec-ref_l-1)
      (λ (i es)
        (ind-Either i
          (λ (i)
            E)
          (λ (i-1) ; just
            (vec-ref_l-1
              i-1 (tail es)))
          (λ (triv) ; nothing
            (head es)))))))

(define vec-ref
  (λ (E l)
    (ind-Nat l
      (λ (k)
        (→ (Fin k) (Vec E k) E))
      (base-vec-ref E)
      (step-vec-ref E))))
```

`base` 代表了 `l` 为 0 的情况。其第二个参数为 `Absurd` 类型（对应 `vecnil`）。由于 `Absurd` 不存在值，所以不可能出现这种情况，可以直接从 `Absurd` 推出目标 `E`。

`step` 要处理两种情况，传入参数 `i`：`(Either (Fin l-1) Trivial)`
- `i` 为 `fzero`：即 `(nothing Trivial)`，返回头部元素
- `i` 为 `fadd1`：即 `(just (Fin i-1))`，递归寻找

## 求解过程

1.
```lisp
(vec-ref Atom 4
  (fadd1 3
    (fzero 2))
  menu)
```

2.
```lisp
((ind-Nat (add1 3)
    (λ (k)
      (→ (Fin k) (Vec Atom k)
        Atom))
    (base-vec-ref Atom)
    (step-vec-ref Atom))
  (fadd1 3
    (fzero 2))
  menu)
```

3.
```lisp
((step-vec-ref Atom (add1 2)
  (ind-Nat (add1 2)
    (λ (k)
      (→ (Fin k) (Vec Atom k)
        Atom))
    (base-vec-ref Atom)
    (step-vec-ref Atom)))
  (fadd1 3
    (fzero 2))
  menu)
```

4.
```lisp
(((λ (E l-1)
    (λ (vec-ref_l-1)
      (λ (f es)
        (ind-Either f
          (λ (i)
            E)
          (λ (i-1)
            (vec-ref_l-1
              i-1 (tail es)))
          (λ (triv)
            (head es))))))
  Atom (add1 2)
  (ind-Nat (add1 2) ...))
  (fadd1 3
    (fzero 2))
  menu)
```

5.
```lisp
(((λ (vec-ref_l-1)
    (λ (f es)
      (ind-Either f
        (λ (i)
          Atom)
        (λ (i-1)
          (vec-ref_l-1
            i-1 (tail es)))
        (λ (triv)
          (head es)))))
  (ind-Nat (add1 2) ...))
  (fadd1 3
    (fzero 2))
  menu)
```

6.
```lisp
((λ (f es)
    (ind-Either f
      (λ (i)
        Atom)
      (λ (i-1)
        ((ind-Nat (add1 2) ...)
          i-1 (tail es)))
      (λ (triv)
        (head es))))
  (fadd1 3
    (fzero 2))
  menu)
```

7.
```lisp
(ind-Either (fadd1 3 (fzero 2))
  (λ (i)
    Atom)
  (λ (i-1)
    ((ind-Nat (add1 2) ...)
      i-1 (tail menu)))
  (λ (triv)
    (head menu)))
```

8.
```lisp
(ind-Either (left (fzero 2))
  (λ (i)
    Atom)
  (λ (i-1)
    ((ind-Nat (add1 2) ...)
      i-1 (tail menu)))
  (λ (triv)
    (head menu)))
```

9.
```lisp
((ind-Nat (add1 2)
    (λ (k)
      (→ (Fin k) (Vec Atom k)
        Atom))
    (base-vec-ref Atom)
    (step-vec-ref Atom))
  (fzero 2)
  (tail menu))
```

10.
```lisp
(step-vec-ref Atom 2
  (ind-Nat (add1 1)
    (λ (k)
      (→ (Fin k) (Vec Atom k)
        Atom))
    (base-vec-ref Atom)
    (step-vec-ref Atom))
  (fzero 2)
  (tail menu))
```

11.
```lisp
((λ (E l-1)
  (λ (vec-ref l-1)
    (λ (f es)
      (ind-Either f
        (λ (i) E)
        (λ (i-1)
          (vec-ref l-1
            i-1 (tail es)))
        (λ (triv)
          (head es))))))
  Atom
  (add1 1)
  (ind-Nat (add1 1) ...)
  (fzero 2)
  (tail menu))
```

12.
```lisp
((λ (f es)
  (ind-Either f
    (λ (i)
      Atom)
    (λ (i-1)
      ((ind-Nat (add1 1) ...)
        i-1 (tail es)))
    (λ (triv)
      (head es))))
  (fzero 2)
  (tail menu))
```

13.
```lisp
(ind-Either (fzero 2)
  (λ (i)
    Atom)
  (λ (i-1)
    ((ind-Nat (add1 1) ...)
      i-1 (tail (tail menu))))
  (λ (triv)
    (head (tail menu))))
```

14.
```lisp
(head (tail menu)) ; 计算完毕
```

# Turner’s Teaser

定义一个函数，接受一个传入一些 `Either` 作为参数的函数 `f`，判断 `f` 是否总会返回 `left`。

方法是遍历所有的输入情况，看看返回是不是都是 `left`。

```lisp
(claim Two
  U)

(define Two
  (Either Trivial Trivial))

(claim Two-Fun
  (→ Nat
    U))

(define Two-Fun
  (λ (n)
    (iter-Nat n
      Two
      (λ (type)
        (→ Two
          type)))))

(claim both-left
  (→ Two Two
    Two))

(define both-left
  (λ (a b)
    (ind-Either a
      (λ (c)
        Two)
      (λ (left-sole)
        b)
      (λ (right-sole)
        (right sole)))))

(claim step-taut
  (Π ((n-1 Nat))
    (→ (→ (Two-Fun n-1)
        Two)
      (→ (Two-Fun (add1 n-1))
        Two))))

(define step-taut
  (λ (n-1 taut_n-1)
    (λ (f)
      (both-left
        (taut_n-1
          (f (left sole)))
        (taut_n-1
          (f (right sole)))))))

(claim taut
  (Π ((n Nat))
    (→ (Two-Fun n)
      Two)))

(define taut
  (λ (n)
    (ind-Nat n
      (λ (k)
        (→ (Two-Fun k)
          Two))
      (λ (x)
        x)
      step-taut)))
```

这里定义了一个 `(Either Trivial Trivial)` 类型 `Two`，下面要做的是判断一个 `(→ Two Two ... Two)` 的函数 `Two-Fun` 是否总是返回 `(left sole)`。

这里的 `Two-Fun` 类型也是递归定义，`(Two-Fun 0)` 返回一个 `Two`，`(Two-Fun n)` 返回一个接受 `n` 个 `Two` 的函数

首先，定义一个函数 `(both-left Two Two)` 判断传入的两个 `Two` 是否都是 `(left sole)`。

不难发现 `f` 有 `n` 个参数，那么可以用 Nat 进行归纳，每次传入一个参数：
- `base`：然后 `f` 是一个 `(Two-Fun 0)`，即一个 `Two`，那么只要返回它本身即可（本身是 `left` 那就是 `left`，否则就是 `right`）
- `step`：对于一个函数 `f`，分别传入一个 `left` 或 `right`，然后递归进行。如果两种情况下返回值都是 `left`，则返回 `left`；否则返回 `right`

例如传入 `(Two-Fun 2 both-left)` 返回 `(left sole)`。

## 看作 Bool

不难发现 `Two` 和 `Bool` 有以下的对应关系：
- `Two` ~ `Bool`
  - `(left sole)` ~ `True`
  - `(right sole)` ~ `False`
- `both-left` ~ `And`
- `taut` ~ `always-true`

所以 `taut` 的目标就是判断一个函数是否是永真的。

```lisp
(claim Bool U)
(define Bool (Either Trivial Trivial))

(claim true Bool)
(define true (left sole))

(claim false Bool)
(define false (right sole))

(claim Bool-Fun (→ Nat U))
(define Bool-Fun
  (λ (n)
    (iter-Nat n
      Bool
      (λ (type) (→ Bool type)))))

(claim and (→ Bool Bool Bool))
(define and
  (λ (a b)
    (ind-Either a
      (λ (_) Bool)
      (λ (_) b)
      (λ (_) false))))

(claim step-taut
  (Π ((n Nat))
    (→ (→ (Bool-Fun n) Bool)
       (→ (Bool-Fun (add1 n)) Bool))))
(define step-taut
  (λ (n taut_n)
    (λ (f) (and (taut_n (f true)) (taut_n (f false))))))

(claim taut (Π ((n Nat)) (→ (Bool-Fun n) Bool)))
(define taut
  (λ (n)
    (ind-Nat n
      (λ (k) (→ (Bool-Fun k) Bool))
      (λ (x) x)
      step-taut)))
```