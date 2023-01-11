---
layout: "post"
title: "「The Little Schemer」 09 ... and Again, and Again, and Again, ..."
subtitle: "无限循环"
author: "roife"
date: 2020-01-06

tags: ["The Little Schemer@读书笔记", "读书笔记@Tags", "Scheme@编程语言", "函数式编程@Tags", "Y 组合子@函数式编程"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# partial functions & total functions

- `(looking a lat)` 表示在 lat 中找 a，寻找方式是，先看第一个元素，如果是数字（比如 i）就跳到第 i 个位置，重复操作，直到找到非数字。判断这个非数字元素是否是 a。

```scheme
(define keep-looking
  (lambda (a sorn lat)
    (cond
     ((number? sorn) (keep-looking a (pick sorn lat) lat))
     (else (eq? sorn a)))))

(define looking
  (lambda (a lat)
    (keep-looking a (pick 1 lat) lat)))
```

`keep-looking` 函数的特点是它并不是对列表 lat 进行调用，所以被称作 unnatural recursion。

但是，keep-looking 有可能不会停机，即它只能接受部分合法的参数，所以被称为 **partial functions**，前面提到的可以接受所有参数的函数被称为 total functions。

- `(shift pair)` 表示让 pair（这个 pair 的第一个元素也是一个 pair）的第一部分的第二个元素和其第二部分形成一个 pair，如 `(shift '((a b) (c d))) => '(a (b (c d)))`

```scheme
(define shift
  (lambda (pair)
    (build (first (first pair))
           (build (second (first pair))
                  (second pair)))))
```

再考虑一下

```scheme
(define align
  (lambda (pora)
    (cond
     ((atom? pora) pora)
     ((a-pair? (first pora))
      (align (shift pora)))
     (else (build (first pora)
                  (align (second pora)))))))
```

这个函数递归的参数并不是原来参数的子序列，可能不停机。

（参见）Commandment 7。

所以我们定义一个 length\* 函数计算其复杂度

- `(length* pora)` 计算 pora 中 atom 的数量

```scheme
(define length*
  (lambda (pora)
    (cond
     ((atom? pora) 1)
     (else(+ (length* (first pora))
             (length* (second pora)))))))
```

然而实际上 align 函数的每次递归都会简化 pora 的第一个参数，因此这个 length\* 参数不能准确判断“参数是否简化”，所以不妨给第一个元素设置一个更高的权重

```scheme
(define weight*
  (lambda (pora)
    (cond
     ((atom? pora) 1)
     (else (+ (* 2 (first (weight* pora))))
           (weight* (second pora))))))
```

这个时候发现 align 函数每次会使得 weight\* 不断减小，因此 align 最后会停机

其实 align 是一个把 list 内元素向右对齐的函数，每次只要头部的元素减少，那么就更加接近目标，所以其复杂度也是减小的。

> 这里提出了一种判断函数是否停机的方法：设置一个价值计算函数，如果价值计算函数的结果不断缩小，则函数最终会停机。

```scheme
(define shuffle
  (lambda (pora)
    (cond
     ((atom? pora) pora)
     ((a-pair? (first pora))
      (shuffle (revpair pora)))
     (else (build (first pora)
                  (shuffle (second pora)))))))
```

这个 shuffle 函数是将 align 函数中的 shift 换成 revpair，但是它不会停机（比如输入 `'((a b) (cd))`) ，因此它是 partial function

- `(eternity x)` 一个不会停机的函数

```scheme
(define eternity
  (lambda (x)
    (eternity x)))
```

- `(C n)` 计算 Collatz 猜想（即 3n+1 问题）

```scheme
(define C
  (lambda (n)
    (cond
     ((one? n) 1)
     ((even? n) (C (quotient n 2)))
     (else (C (add1 (* n 3)))))))
```

> Thanks to Lothar Collatz

- `(A n m)` 计算阿克曼函数

```scheme
(define A
  (lambda (n m)
    (cond
     ((zero? n) (add1 m))
     ((zero? m) (A (sub1 n) 1))
     (else (A (sub1 n)
              (A n (sub1 m)))))))
```

这个函数计算量非常大，即使是 `(A 4 3)` 也算不出来

> Thanks to Wilhelm Ackermann

# 停机问题

停机问题，即是否存在一个函数在有限时间内判断另一个函数会不会停机。

首先假设存在这样的函数 `(will-stop? f)`，显然这必须是一个 total function，返回值为 `\#f` 或者 `\#t`

下面再定义另外一个函数 `(last-try x)`

```scheme
(define last-try
  (lambda (x)
    (and (will-stop? last-try)
         (eternity x)))) ;; eternity 是一个不会停机的函数
```

然后运行 `(will-stop? last-try)`

如果 `(will-stop? last-try)` 为 `\#f`，此时得到了 last-try 的值为 `\#f`，也就是说 last-try 停机了，所以 `(will-stop? last-try)` 的值为 `\#t`，矛盾。同理，如果假设为 `\#t` 仍然得到矛盾。

因此不存在 `(will-stop? f)` 这样的函数。

> Thanks to Alan M. Turing Thanks to Kurt Gödel

# Applicative-order Y combinator

- 首先回顾 length 函数：

```scheme
(define length
  (lambda (l)
    (cond
     ((null? l) 0)
     (else (add1 (length (cdr l)))))))
```

- 现在我们不能用 `define` 定义递归，但是我们还是想实现递归。假设有一个现成的 `self` 函数表示“当前定义的函数”，那么就可以直接用 `self` 进行定义了：

```scheme
(lambda (l)
  (cond
   ((null? l) 0)
   (else (add1 (<self> (cdr l))))))
```

- 但是这个 `self` 究竟是什么？我们还不知道，既然不能用 `<self>`，那么不妨将 `self` 参数化：

```scheme
(lambda (self)
  (lambda (l)
    (cond
     ((null? l) 0)
     (else (add1 (self (cdr l)))))))
```

- 为了方便，不妨给这段程序定义一个名字（这里虽然用了 `define`，但是没用它定义递归）：

```scheme
(define length
  (lambda (self)
    (lambda (l)
      (cond
       ((null? l) 0)
       (else (add1 (self (cdr l))))))))
```

我们想要让程序实现递归，那么不妨在调用时传入自身，即 `((length length) 3)`（这里已经定义了 `length`，所以可以直接用）。

事实上，此时没有用到 `define`，而我们现在已经实现了递归调用！

- 我们可以进一步把 `((length length) x)` 这个过程用高阶函数实现：

```scheme
((lambda (length)
   (length length))
 (lambda (self)
   (lambda (l)
     (cond
      ((null? l) 0)
      (else (add1 (self (cdr l))))))))
```

- 但是这个函数还有一个问题，`self` 为 `(lambda (self) (lambda (l) ...))`，所以 `self` 调用的第一个参数应该是 `self`：

```scheme
((lambda (length)
   (length length))
 (lambda (self)
   (lambda (l)
     (cond
      ((null? l) 0)
      (else (add1 ((self self) (cdr l))))))))
```

- 上面的程序中，`(lambda (l) ...)` 和我们一开始的定义差不多，唯一的区别在于 `<self>` 变成了 `(self self)`。不妨和上面一步一样，将这里的 `(self self)` 再次进行提取出来：

```scheme
((lambda (length)
   (length length))
 (lambda (self)
   ((lambda (self-self)
      (lambda (l)
        (cond
         ((null? l) 0)
         (else (add1 (self-self (cdr l)))))))
    (self self))))

```

- 但是这段代码有一个问题：`(self self)` 这一步没法停机，会不断求值。因此我们需要用 `lambda` 进行包裹，以实现延迟计算：

```scheme
((lambda (length)
    (length length))
  (lambda (self)
    ((lambda (f)
       (lambda (l)
         (cond
          ((null? l) 0)
          (else (add1 (f (cdr l)))))))
     (lambda (x) ((self self) x)))))
```

此时中间的 `(lambda (l) ...)` 那一部分就和我们一开始的定义一模一样！并且仅仅靠外面这一层就实现了递归：

```scheme
((lambda (length)
   (length length))
 (lambda (self)
   ((lambda (f) ...)
    (lambda (x) ((self self) x)))))
```

- 最后，我们将外面这层包装抽象出来：

```scheme
((lambda (le)
   ((lambda (length)
      (length length))
    (lambda (self)
      (le (lambda (x) ((self self) x))))))
 (lambda (f)
   (lambda (l)
     (cond
      ((null? l) 0)
      (else (add1 (f (cdr l))))))))
```

- 我们就得到了 **Applicative-order Y combinator**：

```scheme
(define Y
  (lambda (le)
    ((lambda (f) (f f))
     (lambda (f)
       (le (lambda (x) ((f f) x)))))))
```
