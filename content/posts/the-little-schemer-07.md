+++
title = "[The Little Schemer] 07 Friends and Relations"
author = ["roife"]
date = 2020-01-05
series = ["The Little Schemer"]
tags = ["程序语言理论", "scheme", "函数式编程"]
draft = false
+++

## 集合 {#集合}

set 是一个不包含重复元素的 lat

-   `(set? lat)` 判断 lat 是否是一个 set

<!--listend-->

```scheme
(define set?
  (lambda (lat)
    (cond
     ((null? lat) #t)
     ((member? (car lat) (cdr lat)) #f)
     (else (set? (cdr lat))))))
```

-   `(makeset lat)` 去掉 lat 中的重复元素使其成为 set

<!--listend-->

```scheme
(define makeset
  (lambda (lat)
    (cond
     ((null? lat) '())
     ((member? (car lat) (cdr lat)) (makeset (cdr lat)))
     (else (cons (car lat) (makeset (cdr lat)))))))

(define makeset-multirember
  (lambda (lat)
    (cond
     ((null? lat) '())
     (else (cons (car lat)
                 (makeset-multirember (car lat) (cdr lat)))))))
```

-   `(subset? set1 set2)` 判断 set1 是否为 set2 的子集

<!--listend-->

```scheme
(define subset?
  (lambda (set1 set2)
    (cond
     ((null? set1) #t)
     ((member? (car set1) set2) (subset? (cdr set1) set2))
     (else #f))))

(define subset?-and
  (lambda (set1 set2)
    (cond
     ((null? set1) #t)
     (and (member (car set1) set2)
          (subset?-and (cdr set1) set2)))))
```

-   `(eqset? set1 set2)` 判断两个 set 是否相等

<!--listend-->

```scheme
(define eqset?
  (lambda (set1 set2)
    (and (subset? set1 set2)
         (subset? set2 set1))))
```

-   `(intersect? set1 set2)` 判断两个 set 是否有交集

<!--listend-->

```scheme
(define intersect?
  (lambda (set1 set2)
    (cond
     ((null? set1) #f)
     ((member? (car set1) set2) #t)
     (else (intersect? (cdr set1) set2)))))
```

-   `(intersect set1 set2)` 求 set1 and set2

<!--listend-->

```scheme
(define intersect
  (lambda (set1 set2)
    (cond
     ((null? set1) '())
     ((member? (car set1) set2) (cons (car set1)
                                      (intersect (cdr set1) set2)))
     (else (intersect (cdr set1) set2)))))
```

-   `(union set1 set2)` 求 set1+set2

<!--listend-->

```scheme
(define union
  (lambda (set1 set2)
    (cond
     ((null? set1) set2)
     ((member? (car set1) set2) (union (cdr set1) set2))
     (else (cons (car set1)
                 (union (cdr set1) set2))))))
```

-   `(xxx set1 set2)` 返回 set1-set2

<!--listend-->

```scheme
(define xxx
  (lambda (set1 set2)
    (cond
     ((null? set1) '())
     ((member? (car set1) set2) (xxx (cdr set1) set2))
     (else (cond (car set1)
                 (xxx (cdr set1) set2))))))
```

-   `(intersectall l-set)` l-set 是一个一重集合构成的集合，求这些一重集合构成的交

<!--listend-->

```scheme
(define intersectall
  (lambda (l-set)
    (cond
     ((null? (cdr l-set)) (car l-set))
     (else (intersect (car l-set)
                      (intersectall (cdr l-set)))))))
```


## pair {#pair}

Scheme 中将两个不同含义但是有关联的元素组成的 list 称作 pair

-   `(a-pair? x)` 判断 x 是否为 pair

<!--listend-->

```scheme
(define a-pair?
  (lambda (x)
    (cond
     ((atom? x) #f)
     ((null? x) #f)
     ((null? (cdr x)) #f)
     ((null? (cdr (cdr x))) #t)
     (else #f))))
```

下面是 pair 相关的操作

-   `(first p)` 获取 pair 的一个元素
-   `(second p)` 获取 pair 的第二个元素
-   `(build s1 s2)` 将 s1 与 s2 组成 pair

<!--listend-->

```scheme
(define first (lambda (p) (car p)))
(define second (lambda (p) (car (cdr p))))
(define build (lambda (s1 s2) (cons s1 (cons s2 '())))) ;; 注意
```

由 pair 组成的 set 被称为 rel（relation，即关系，常指二元关系，可以看作是多值函数的映射）

当 rel 变为单射时即为 fun（function，&lt;数、&gt;函数）

```scheme
(define fun?
  (lambda (rel)
    (set? (firsts rel))))
```

-   `(fun? rel)` 判断一个 rel 是否为函数

-   `(reveal rel)` 构建反向映射关系，即交换每一个 pair 的 first 和 second

<!--listend-->

```scheme
(define reveal
  (lambda (rel)
    (cond
     ((null? rel) '())
     (else (cons (build (first (car rel))
                        (second (car rel)))
                 (reveal (cdr rel))))))) ;; 注意此处的小函数使得可读性提升
```

-   `(revpair pair)` 交换一个 pair 的两个元素

<!--listend-->

```scheme
(define revpair
  (lambda (pair)
    (build (first pair) (second pair))))
```

可以用这个函数进一步简化 reveal

-   `(fullfun? fun)` 判断一个函数是否可逆（一一映射）

<!--listend-->

```scheme
(define fullfun?
  (lambda (fun)
    (fun? (reveal fun))))
```

> 这一章通过 scheme 构建了集合及其操作，并以此为基础构建了映射关系、函数、一一映射等。
>
> 本章展现了通过小函数来构建大函数有益于代码可读性的增强
