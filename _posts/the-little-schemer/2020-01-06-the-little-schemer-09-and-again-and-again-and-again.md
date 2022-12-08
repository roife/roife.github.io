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

首先假设存在这样的函数 `(will-stop? f)`，显然这必须是一个 total function，返回值为 \#f 或者 \#t

下面再定义另外一个函数 `(last-try x)`

```scheme
(define last-try
  (lambda (x)
    (and (will-stop? last-try)
         (eternity x)))) ;; eternity 是一个不会停机的函数
```

然后运行 `(will-stop? last-try)`

那么会发现如果希望计算出 `(will-stop? last-try)`，就必须先计算出 `(will-stop? last-try)`

如果 `(will-stop? last-try)` 为 \#f，那么 `(and (will-stop? last-try) (eternity x))))` 也是 \#f，此时得到了 last-try 的值，也就是说 last-try 停机了，所以
`(will-stop? last-try)` 的值为 \#t，矛盾。同理，如果假设为 \#t 仍然得到矛盾。

因此不存在 `(will-stop? f)` 这样的函数。

> Thanks to Alan M. Turing Thanks to Kurt Gödel

# applicative-order Y combinator

首先回顾 length 函数

```scheme
(define length
  (lambda (l)
    (cond
     ((null? l) 0)
     (else (add1 (length (cdr l)))))))
```

## 展开递归

考虑一个只能计算 null list 的 length0

```scheme
(lambda (l)
  (cond
   ((null? l) 0)
   (else (add1 (eternity (cdr l))))))
```

它还可以进一步变化成 length1，可以计算长度小于等于 1 的函数

```scheme
(lambda (l)
  (cond
   ((null? l) 0)
   (else (add1 ((lambda (l) ;; 这里开始进一步变化
                  (cond
                   ((null? l) 0)
                   (else (add1 (enterity (cdr l))))))
                (cdr l))))))
```

同样还可以构造出 lengthN，但是没有递归所以无法计算任意长度的列表。但是可以发现展开的一部分内容是重复的，把这一部分抽象出来变成
(lambda (l)) 后重写 length0

```scheme
((lambda (length)
   (lambda (l)
     (cond
      ((null? l) 0)
      (else (add1 (length (cdr l)))))))
 eternity)
```

同样可以写出 length1，length2…

```scheme
((lambda (f)
   (lambda (l)
     (cond
      ((null? l) 0)
      (else (add1 (f (cdr l)))))))
 ((lambda (g)
    (lambda (l)
      (cond
       ((null? l) 0)
       (else (add1 (g (cdr l)))))))
  enternity))
```

把主题部分独立成一个 lambda 函数后，尝试复用它，用 mk-length 来实现。

```scheme
((lambda (mk-length)
   (mk-length eternity))
 (lambda (length)
   (lambda (l)
     (cond
      ((null? l) 0)
      (else (add1 (length (cdr l))))))))
```

同样可以写出 length2，…

```scheme
((lambda (mk-length)
   (mk-length
    (mk-length eternity)))
 (lambda (length)
   (lambda (l)
     (cond
      ((null? l) 0)
      (else (add1 (length (cdr l))))))))
```

## 实现调用

不难发现每次要把 eternity 传给 mk-length 的时候程序就到了尽头（即无法停机），但是我们希望这时能继续调用 mk-length 继续形成调用链（lengthN -\> lengthN-1 -\> … -\> length0），因此使用
`(mk-length mk-length)` 就可以进行自我调用

同时为了让代码看起来更一致，同时把 length 换成 mk-length

这样就写出了 length0 (mk-length 只接受另一个函数，超过 0 的 list 会传入 `(cdr l)` 导致问题）

```scheme
((lambda (mk-length)
   (mk-length mk-length))
 (lambda (mk-length)
   (lambda (l)
     (cond
      ((null? l) 0)
      (else (add1 (mk-length (cdr l)))))))) ;; MARK
```

现在想要多调用一层只要把 MARK 部位的 mk-length 换成 `(mk-length eternity)`

```scheme
((lambda (mk-length)
   (mk-length mk-length))
 (lambda (mk-length)
   (lambda (l)
     (cond
      ((null? l) 0)
      (else (add1 ((mk-length eternity) (cdr l)))))))) ;; MARK
```

现在，函数展开后相当于两层 length 后出现了 eternity，如果要继续调用那么还要把这里的 eternity 改成 mk-length（注意这个 mk-length 的含义是 `(lambda (mk-length))` 这个部分）

```scheme
((lambda (mk-length)
   (mk-length mk-length))
 (lambda (mk-length)
   (lambda (l)
     (cond
      ((null? l) 0)
      (else (add1 ((mk-length mk-length) (cdr l))))))))
```

新函数最大的区别是多了 `(mk-length mk-length)`，所以尝试把这一部分抽象出来

```scheme
((lambda (mk-length)
   (mk-length mk-length))
 (lambda (mk-length)
   ((lambda (length)
      (lambda (l)
        (cond
         ((null? l) 0)
         (else (add1 (length (cdr l)))))))
    (mk-length mk-length))))
```

但是这段代码无法停机，因为它会不断展开自身而无法进入计算（因为我们抽象并把调用自己的过程放到了外面，所以它会先展开，而不是和原来一样先计算）

正确的做法是让这段在运行到这个位置时再进行展开，所以为了防止它提前计算，可以把这个封装成函数，在调用的时候才展开

```scheme
((lambda (mk-length)
   (mk-length mk-length))
 (lambda (mk-length)
   ((lambda (length)
      (lambda (l)
        (cond
         ((null? l) 0)
         (else (add1 (length (cdr l)))))))
    (lambda (x) (mk-length mk-length)))))
```

## 提取应用序 Y 组合子

最后，我们把计算的过程和函数组合的过程分开，就变成了

```scheme
((lambda (le)
   ((lambda (mk-length)
      (mk-length mk-length))
    (lambda (mk-length)
      (le (lambda (x) ((mk-length mk-length) x)))))) ;; applicative-order Y combinatior

 (lambda (length)
   (lambda (l)
     (cond
      ((null? l) 0)
      (else (+ 1 (length (cdr l))))))))
```

所以我们就得到了 **Applicative-order Y combinator**

```scheme
(define Y
  (lambda (le)
    ((lambda (f) (f f))
     (lambda (f)
       (le (lambda (x) ((f f) x)))))))
```
