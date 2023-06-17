+++
title = "[The Little Schemer] 01 Toys ~ 04 Number Games"
author = ["roife"]
date = 2020-01-03
series = ["The Little Schemer"]
tags = ["程序语言理论", "scheme", "函数式编程"]
draft = false
+++

## 01 Toys {#01-toys}


### atom 与 list {#atom-与-list}

atom 与 list 都是 S-expr

-   `()` 被称为 null list，也是一个 list
-   `'atom` 等价于 `(quote atom)`，`'list` 等价于 `(quote list)`


## 02 Do It, Do It Again, and Again, and Again... {#02-do-it-do-it-again-and-again-and-again-dot-dot-dot}


### 列表 {#列表}

-   `(car l)` 表示取出 list 的第一个元素，结果可以是 atom 也可以是 list，如 `(car '((a b c) x y z)) => '(a b c)`
-   `(cdr l)` 表示取出 list 里除了第一个元素的剩下部分，如 `(cdr '((a b c) x y z)) => '(x y z)`，当 list 只有一个元素时返回 `()`

`car` 与 `cdr` 都不可对 atom 或者 null list 操作

-   `(cons x l)` 表示把一个元素加到另一个 list 的头部，返回一个 list，如 `(cons 'a (car '((b) c d))) => '(a b)`，第一个参数随意，第二个参数必须是 list

可以用 `(cons atom '())` 构建一个表 `'(atom)`

-   `(null? l)` 表示判断 list 是否为 null，如 `(null? '(a)) => #f`，参数必须是 list

<!--listend-->

```scheme
(define atom?
  (lambda (x)
    (and (not (pair? x))
         (not (null? x)))))
```

-   `(eq? a b)` 表示判断两个 atom 是否相等，如 `(eq? 'a 'a) => #`，参数必须是非数字的 atom，不可以是 list
-   `(lat? lat)` 表示判断一个 list 全部都是由 atom 组成，如 `(lat? '(a b (c))) => #f`，对于 null list 也返回 `#t`

<!--listend-->

```scheme
(define lat?
  (lambda (l)
    (cond
     ((null? l) #t)
     ((atom? (car l)) (lat? (cdr l)))
     (else #f))))
```

> 本章介绍了 scheme 的基本操作，其中最为重要的是 cond 的使用。模式匹配是 scheme 强大的武器，贯穿了这本书，
>
> 也是函数式编程的重要思考方式。


## 03 Cons the Magnificent {#03-cons-the-magnificent}


### 简单列表函数 {#简单列表函数}

-   `(member? a lat)` 表示判断一个 atom 是否为一个 lat 的一部分，如 `(member? 'a '(a b c)) => #t`

<!--listend-->

```scheme
(define member?
  (lambda (a lat)
    (cond
     ((null? lat) #f)
     ((eq? a (car lat)) #t)
     (else (member? a (cdr lat))))))
```

-   `(rember a lat)` 表示从一个 lat 中移除一个 atom 第一次出现的地方，如 `(rember 'mint '(mint lamb chops mint)) => '(lamb chops)`，若未出现则不改变

<!--listend-->

```scheme
(define rember
  (lambda (a lat)
    (cond
     ((null? lat) '())
     ((eq? a (car lat)) (cdr lat))
     (else (cons (car lat)
                 (rember a (cdr lat)))))))
```

-   `(firsts l)` 表示取出 list 中每一个子列表的第一个元素，来组成新列表，如 `(firsts '((a b) (c d) (e f))) => '(a c e)`

<!--listend-->

```scheme
(define firsts
  (lambda (l)
    (cond
     ((null? l) '())
     (else (cons (car (car l)) (firsts (cdr l)))))))
```

-   `(insertR a b lat)` 表示把 atom a 插入到 lat 里 atom b 第一次出现的位置后，如 `(insertR 'a 'b '(c d b)) => '(c d b a)`

<!--listend-->

```scheme
(define insertR
  (lambda (a b lat)
    (cond
     ((null? lat) '())
     ((eq? b (car lat)) (cons b
                              (cons a (cdr lat))))
     (else (cons (car lat)
                 (insertR a b (cdr lat)))))))
```

```scheme
(define insertL
  (lambda (a b lat)
    (cond
     ((null? lat) '())
     ((eq? b (car lat)) (cons a lat))
     (else (cons (car lat)
                 (insertL a b (cdr lat)))))))
```

-   `(subst a b lat)` 表示用 atom a 替换第一个 atom b，如 `(subst 'a 'b '(c b)) => '(c a)`

<!--listend-->

```scheme
(define subst
  (lambda (a b lat)
    (cond
     ((null? lat) '())
     ((eq? b (car lat)) (cons a (cdr lat)))
     (else (cons (car lat)
                 (subst a b (cdr lat)))))))
```

-   `(subst2 a b c lat)` 表示用 atom a 替换 atom b 或第一个 atom c ，如 `(subst2 'a 'b '(c b)) => '(c a)`

<!--listend-->

```scheme
(define subst2
  (lambda (a b c lat)
    (cond
     ((null? lat) '())
     ((or (eq? b (car lat))
          (eq? c (car lat))) (cons a (cdr lat)))
     (else (cons (car lat)
                 (subst2 a b c (cdr lat)))))))
```


### 多次操作的列表函数 {#多次操作的列表函数}

-   `(multirember a lat)` 表示删除 lat 中所有的 atom a

<!--listend-->

```scheme
(define multirember
  (lambda (a lat)
    (cond
     ((null? lat) '())
     ((eq? a (car lat)) (multirember a (cdr lat)))
     (else (cons (car lat)
                 (multirember a (cdr lat)))))))
```

-   `(multiinsertR a b lat)` 表示在所有的 atom b 后面插入 atom a

<!--listend-->

```scheme
(define multiinsertR
  (lambda (a b lat)
    (cond
     ((null? lat) '())
     ((eq? b (car lat)) (cons b
                              (cons a (multiinsertR a b (cdr lat)))))
     (else (cons (car lat)
                 (multiinsertR a b (cdr lat)))))))
```

-   `(multiinsertR a b lat)` 表示在所有的 atom b 前面插入 atom a

<!--listend-->

```scheme
(define multiinsertL
  (lambda (a b lat)
    (cond
     ((null? lat) '())
     ((eq? b (car lat)) (cons a (cons b (multiinsertL a b (cdr lat))))) ; 注意这个地方
     (else (cons (car lat)
                 (multiinsertL a b (cdr lat)))))))
```

-   `(multisubst a b lat)` 表示把所有的 atom b 替换成 atom a

<!--listend-->

```scheme
(define multisubst
  (lambda (a b lat)
    (cond
     ((null? lat) '())
     ((eq? b (car lat)) (cons a (multisubst a b (cdr lat))))
     (else (cons (car lat)
                 (multisubst a b (cdr lat)))))))
```


## 04 Number Games {#04-number-games}


### 普通数字操作 {#普通数字操作}

下面只考虑非负整数。

-   `(add1 x)` 返回 x+1
-   `(sub1 x)` 返回 x-1
-   `(zero? x)` 判断 x 是否为 0
-   `(o+ m n)` 返回 m+n
-   `(o- m n)` 返回 m-n

<!--listend-->

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

-   tup 表示一个纯数字构成的 list，如 `'(1 2 3)`，`()` 称作 null tup

下面尝试将列表操作对应到数字操作

tup 的判空语句和 list 一样，都是 `(null? tup)`。同时，在数字运算中，`((null? l) '())` 变为了 `((null? tup) 0)`

-   `(addtup tup)` 求出 tup 中所有数字之和

<!--listend-->

```scheme
(define addtup
  (lambda (tup)
    (cond
     ((null? tup) 0)
     (else (o+ (car tup)
               (addtup (cdr tup)))))))
```

-   `(o* a b)` 返回 a\*b

<!--listend-->

```scheme
(define o*
  (lambda (a b)
    (cond
     ((zero? b) 0)
     (else (o+ a (o* a (sub1 b)))))))
```

-   `(tup+ tup1 tup2)` 将 tup1 中元素与 tup2 中对应位置的元素相加，对于空元素视为 0，如 `(tup+ '(1 2 3) '(3 4)) => '(4 6 3)`

<!--listend-->

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

-   `(> a b)` 返回 a&gt;b

<!--listend-->

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

-   `(` a b)= 返回 `a=b`

<!--listend-->

```scheme
(define =
  (lambda (a b)
    (cond
     ((> a b) #f)
     ((< a b) #f)
     (else #t))))
```

`=` 等价于 `eq?`

-   `(^ a b)` 计算 `a^b`

<!--listend-->

```scheme
(define ^
  (lambda (a b)
    (cond
     ((zero? b) 1)
     (else (o* a (^ a (sub1 b)))))))
```

-   `(o/ a b)` 计算 a/b

<!--listend-->

```scheme
(define o/
  (lambda (a b)
    (cond
     ((zero? a) 0)
     (else (add1 (o/ (o- a b) b))))))
```


### 列表中的数字运算 {#列表中的数字运算}

-   `(length lat)` 计算 lat 的长度

<!--listend-->

```scheme
(define length
  (lambda (lat)
    (cond
     ((null? lat) 0)
     (else (add1 (length (cdr lat)))))))
```

-   `(pick n lat)` 返回计算 lat 中第 n 个元素

<!--listend-->

```scheme
(define pick
  (lambda (n lat)
    (cond
     ((zero? (sub1 n)) (car lat))
     (else (pick (sub1 n) (cdr lat))))))
```

-   `(rempick n lat)` 返回去掉第 n 个元素后的 lat

<!--listend-->

```scheme
(define rempick
  (lambda (n lat)
    (cond
     ((zero? (sub1 n)) (cdr lat)) ; 注意
     (else (cons (car lat)
                 (rempick (sub1 n) (cdr lat)))))))
```

-   `(number? n)` 判断 n 是否为数字，注意这个函数是基础函数，无法表达

-   `(non-nums lat)` 去除 lat 中所有的数字

<!--listend-->

```scheme
(define non-nums
  (lambda (lat)
    (cond
     ((null? lat) '())
     ((number? (car lat)) (non-nums (cdr lat)))
     (else (cons (car lat)
                 (non-nums (cdr lat)))))))
```

-   `(all-nums lat)` 提取出 lat 中所有数字组成 tup

<!--listend-->

```scheme
(define all-nums
  (lambda (lat)
    (cond
     ((null? lat) '())
     ((number? (car lat)) (cons (car lat)
                                (all-nums (cdr lat))))
     (else (all-nums (cdr lat))))))
```

-   `(eqan? a b)` 比较 a 和 b 是否相同（考虑数字和普通 atom）

<!--listend-->

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

-   `(occur a lat)` 统计 a 在 lat 中出现的次数

<!--listend-->

```scheme
(define occur
  (lambda (a lat)
    (cond
     ((null? lat) 0)
     ((eq? (car lat) a) (add1 (occur a (cdr lat))))
     (else (occur a (cdr lat))))))
```
