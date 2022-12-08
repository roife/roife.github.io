---
layout: "post"
title: "「The Little Typer」 16 If it's all the same to you"
subtitle: "可判定性"
author: "roife"
date: 2021-04-10

tags: ["The Little Typer@读书笔记", "读书笔记@Tags", "Dependent Type@程序语言理论", "形式化验证@程序语言理论", "Pie@编程语言", "类型系统@程序语言理论", "程序语言理论@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# `zero?`

前面提到过一个 `(zerop n)`，判断 `n` 是否为 0，返回 `'t` 或 `'nil`，其类型为 `(→ Nat Atom)`。然而从类型上并不能看出来它返回的是哪一个 Atom。下面用 `Dec` 写一个新的判断 0 的函数，可以看出具体的返回值，并且将判断和证明结合在了一起：

> For every Nat j, it is decidable whether j equals zero.

```lisp
(claim zero?
  (Π ((j Nat))
    (Dec
      (= Nat zero j))))
; (Either
;   (= Nat zero n)
;   (→ (= Nat zero n)
;     Absurd))
(define zero?
  (λ (j)
    (ind-Nat j
      (λ (k)
        (Dec (= Nat zero k)))
      (left
        (same zero)) ; (= 0 0)
      (λ (j-1 zero?_j-1)
        (right
          (zero-not-add1 j-1)))))) ; (= 0 (add1 j)) => Absurd
```

# `nat?`

> For every two natural numbers n and j, it is decidable whether n equals j.

```lisp
(claim nat=?
  (Π ((n Nat)
      (j Nat))
    (Dec (= Nat n j))))
```

## motive

```lisp
(claim mot-nat=?
  (→ Nat
    U))

(define mot-nat=?
  (λ (k)
    (Π ((j Nat))
      (Dec
        (= Nat k j)))))
; For every Nat j, it is decidable whether j is equal to the target.
```

比较 `mot-nat=?` 和 `mot-front` 可以发现，二者都为 motive 添加了额外的参数来构建更精确的类型。不同之处在于 `mot-front` 是考虑到 `base` 到类型可能是一个谬模式，而 `mot-nat=?` 引入参数 `j` 是为了让返回的类型更 general，即返回的类型中的 `j` 也是一个变量。这个做法类似于 Coq 里面 `induction` 一个变量后对另一个变量进行 `generalize dependent`。

`base` 针对的是 `n` 为 `zero` 的情况，其类型为：

```lisp
(Π ((j Nat))
  (Dec
    (= Nat zero j)))
```

即用 `zero?` 判断。

## `step`

```lisp
(claim step-nat=?
  (Π ((n-1 Nat))
    (→ (mot-nat=? n-1)
      (mot-nat=? (add1 n-1)))))

;; (= (add1 n) 0) => Absurd
(claim add1-not-zero
  (Π ((n Nat))
    (→ (= Nat (add1 n) zero)
      Absurd)))

(define add1-not-zero
  (λ (n)
    (use-Nat= (add1 n) zero)))

; check (= (add1 (add1 n-1) j))
(define step-nat=?
  (λ (n-1 nat=?_n-1)
    (λ (j)
      (ind-Nat j
        (λ (k)
          (Dec
            (= Nat (add1 n-1) k)))
        (right
          (add1-not-zero n-1)) ; (= 0 (add1 n-1)) => Absurd
        (λ (j-1 nat=?_n-1_2)
          ???))))) ; need a step
```

`step-nat=?` 对 `j` 进行 `ind-Nat` 归纳证明，针对的是 `n` 为 `(add1 n-1)` 的情况。

`base` 是 `(= (add1 n-1) 0)`，即 `Absurd`。这里定义了一个 `add1-not-zero`，类似于 `zero-not-add1`。

### `step` for `step-nat=?`

`step` 的返回类型为 `(= (add1 n-1) (add1 j-1))`，其类型为：

```lisp
(Π ((j-1 Nat))
  (→ (Dec (= Nat (add1 n-1) j-1))
    (Dec (= Nat (add1 n-1) (add1 j-1)))))
```

显然这里的 `nat=?_n-1_2` 是用不到的，因为 `(= Nat (add1 n-1) j-1)` 不能推出 `(= Nat (add1 n-1) (add1 j-1))`。也就是说在构建 `step-nat=?` 的时候，不能用 `step` 的上次证明的结果递推出这次的结果。通常使用归纳法的时候，需要用 `j-1` 的结果证明 `j` 的情况。然而假设 `j-1 = n`，并不能推出 `j = n`。

所以写 `step` 的时候，不得不使用 `step-nat=?` 的 `nat=?_n-1`，其类型为：

```lisp
(Π ((j Nat))
  (Dec
    (= Nat n-1 j)))
```

这就是为什么前面的 `mot-nat=?` 要在返回类型中加入 Π。
- 如果没有加入 Π，则 `nat=?_n-1` 里面的 `j` 是一个常量，即最开始的 `j`
- 而加入了 Π 后，`nat=?_n-1` 里面的 `j` 是一个变量。通过传入不同的 `j`，可以得到不同的 `(Dec (= Nat n-1 j))`，代表的含义是 `n-1` 与 `j` 的等价性。所以通过 `nat=?_n-1` 可以得到 `n-1` 和其他所有 `j` 的等价性，包括 `j-1`。

需要注意的是这里向 `nat=?_n-1` 传入参数得到的是 `(Dec (= Nat n-1 j-1))` 而不是 `(= Nat n-1 j-1)`。对于前者来说，既可以是相等的情况（`left`），也可以是不等（`right`）。具体取决于传入的 `j-1`。而对于后者则只有“等于”这一种情况。

向 `nat=?_n-1` 传入 `j-1`，即 `(nat=?_n-1 j-1)`，其类型为 `(Dec (= Nat n-1 j-1))`。而我们需要构建的是 `(Dec (= Nat (add1 n-1) (add1 j-1)))`。这里借助一个新的辅助函数。

### `dec-add1=`

- 如果 `(Dec (= Nat n-1 j-1))` 是 `left`，即 `n-1 = j-1`，则直接用 `cong`
- 否则如果是 `right`，即 `n-1 != j-1`，则直接用 `sub1=`

```lisp
(claim dec-add1=
  (Π ((n-1 Nat)
      (j-1 Nat))
  (→ (Dec (= Nat n-1 j-1))
    (Dec (= Nat (add1 n-1) (add1 j-1))))))

(define dec-add1=
  (λ (n-1 j-1 eq-or-not)
    (ind-Either eq-or-not
      (λ (target)
        (Dec (= Nat (add1 n-1) (add1 j-1))))
      (λ (yes)
        (left (cong yes (+ 1))))
      (λ (no)
        (right
          (λ (n=j)
            (no
              (sub1= n-1 j-1 n=j))))))))
```

注意 `right` 的情况，其类型为：

```lisp
(→ (→ (= Nat n-1 j-1)
    Absurd)
  (→ (= Nat (add1 n-1) (add1 j-1)))
    Absurd)
```

令 `no` 为 `(→ (= Nat n-1 j-1) Absurd)`，`n=j` 为 `(= Nat (add1 n-1) (add1 j-1)))`。

则 `(sub1= n-1 j-1 n=j)` 为 `(= Nat n-1 j-1)`，则 `(no (sub1= n-1 j-1 n=j))` 为 `Absurd`。

### `step-nat=?`

```lisp
(define step-nat=?
  (λ (n-1 nat=?_n-1)
    (λ (j)
      (ind-Nat j
        (λ (k)
          (Dec
            (= Nat (add1 n-1) k)))
        (right
          (add1-not-zero n-1)) ; (= 0 (add1 n-1)) => Absurd
        (λ (j-1 nat=?_n-1_2)
          (dec-add1= n-1 j-1
            (nat=?_n-1 n-1)))))))
```

## `nat=?`

```lisp
(define nat=?
  (λ (n j)
    ((ind-Nat n
        mot-nat=?
        zero?
        step-nat=? )
    j)))
```

> `nat=?` is both a proof that makes a statement true and a function that determines whether any two numbers are equal.