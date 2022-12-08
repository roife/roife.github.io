---
layout: "post"
title: "「The Little Schemer」 04 Number Games"
subtitle: "数字操作"
author: "roife"
date: 2020-01-03

tags: ["The Little Schemer@读书笔记", "读书笔记@Tags", "Scheme@编程语言", "函数式编程@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 普通数字操作

下面只考虑非负整数。

- `(add1 x)` 返回 x+1

- `(sub1 x)` 返回 x-1

- `(zero? x)` 判断 x 是否为 0

- `(o+ m n)` 返回 m+n

- `(o- m n)` 返回 m-n

```scheme
(define o+
  (lambda (m n)
    (cond
     ((zero? m) n)
     (else (add1 (o+ n (sub1 m)))))))

(define o-
  (lambda (m n)
    (cond
     ((zero? m) n)
     (else (sub1 (o- n (sub1 m)))))))
```

可以发现数字操作可以与列表操作对应，`zero?` 对应 `null?`，`add1` 对应 `cons`

- tup 表示一个纯数字构成的 list，如 `'(1 2 3)`，`()` 称作 null tup

下面尝试将列表操作对应到数字操作

tup 的判空语句和 list 一样，都是 `(null? tup)`。同时，在数字运算中，`((null? l) '())` 变为了
`((null? tup) 0)`

- `(addtup tup)` 求出 tup 中所有数字之和

```scheme
(define addtup
  (lambda (tup)
    (cond
     ((null? tup) 0)
     (else (o+ (car tup)
               (addtup (cdr tup)))))))
```

- `(o* a b)` 返回 a\*b

```scheme
(define o*
  (lambda (a b)
    (cond
     ((zero? b) 0)
     (else (o+ a (o* a (sub1 b)))))))
```

- `(tup+ tup1 tup2)` 将 tup1 中元素与 tup2 中对应位置的元素相加，对于空元素视为 0，如 `(tup+ '(1 2 3) '(3 4)) => '(4 6 3)`

```scheme
(define tup+
  (lambda (tup1 tup2)
    (cond
     ((and (null? tup1)
           (null? tup2)) '())
     ((null? tup1) tup2)
     ((null? tup2) tup1)
     (else (cons (o+ (car tup1) (car tup2))
                 (tup+ (cdr tup1) (cdr tup2)))))))
```

- `(> a b)` 返回 a\>b

```scheme
(define >
  (lambda (a b)
    (cond
     (and (zero? a)
          (zero? b) #f)
     ((zero? a) #f)
     ((zero? b) #t)
     (else (> (sub1 a) (sub1 b))))))
```

- `(= a b)` 返回 `a=b`

```scheme
(define =
  (lambda (a b)
    (cond
     ((> a b) #f)
     ((< a b) #f)
     (else #t))))
```

`=` 等价于 `eq?`

- `(^ a b)` 计算 `a^b`

```scheme
(define ^
  (lambda (a b)
    (cond
     ((zero? b) 1)
     (else (o* a (^ a (sub1 b)))))))
```

- `(o/ a b)` 计算 a/b

```scheme
(define o/
  (lambda (a b)
    (cond
     ((zero? a) 0)
     (else (add1 (o/ (o- a b) b))))))
```

# 列表中的数字运算

- `(length lat)` 计算 lat 的长度

```scheme
(define length
  (lambda (lat)
    (cond
     ((null? lat) 0)
     (else (add1 (length (cdr lat)))))))
```

- `(pick n lat)` 返回计算 lat 中第 n 个元素

```scheme
(define pick
  (lambda (n lat)
    (cond
     ((zero? (sub1 n)) (car lat))
     (else (pick (sub1 n) (cdr lat))))))
```

- `(rempick n lat)` 返回去掉第 n 个元素后的 lat

```scheme
(define rempick
  (lambda (n lat)
    (cond
     ((zero? (sub1 n)) (cdr lat)) ; 注意
     (else (cons (car lat)
                 (rempick (sub1 n) (cdr lat)))))))
```

- `(number? n)` 判断 n 是否为数字，注意这个函数是基础函数，无法表达

- `(non-nums lat)` 去除 lat 中所有的数字

```scheme
(define non-nums
  (lambda (lat)
    (cond
     ((null? lat) '())
     ((number? (car lat)) (non-nums (cdr lat)))
     (else (cons (car lat)
                 (non-nums (cdr lat)))))))
```

- `(all-nums lat)` 提取出 lat 中所有数字组成 tup

```scheme
(define all-nums
  (lambda (lat)
    (cond
     ((null? lat) '())
     ((number? (car lat)) (cons (car lat)
                                (all-nums (cdr lat))))
     (else (all-nums (cdr lat))))))
```

- `(eqan? a b)` 比较 a 和 b 是否相同（考虑数字和普通 atom）

```scheme
(define eqan?
  (lambda (a b)
    (cond
     ((and (number? a)
           (number? b) (= a b)))
     ((or (number? a)
          (number? b)) #f)
     (else (eq? a b)))))
```

- `(occur a lat)` 统计 a 在 lat 中出现的次数

```scheme
(define occur
  (lambda (a lat)
    (cond
     ((null? lat) 0)
     ((eq? (car lat) a) (add1 (occur a (cdr lat))))
     (else (occur a (cdr lat))))))
```
