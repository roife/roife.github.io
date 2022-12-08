---
layout: "post"
title: "「The Little Schemer」 03 Cons the Magnificent"
subtitle: "Cons 与 列表"
author: "roife"
date: 2020-01-03

tags: ["The Little Schemer@读书笔记", "读书笔记@Tags", "Scheme@编程语言", "函数式编程@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 简单列表函数

- `(member? a lat)` 表示判断一个 atom 是否为一个 lat 的一部分，如 `(member? 'a '(a b c)) => #t`

```scheme
(define member?
  (lambda (a lat)
    (cond
     ((null? lat) #f)
     ((eq? a (car lat)) #t)
     (else (member? a (cdr lat))))))
```

- `(rember a lat)` 表示从一个 lat 中移除一个 atom 第一次出现的地方，如 `(rember 'mint '(mint lamb chops mint)) => '(lamb chops)`，若未出现则不改变

```scheme
(define rember
  (lambda (a lat)
    (cond
     ((null? lat) '())
     ((eq? a (car lat)) (cdr lat))
     (else (cons (car lat)
                 (rember a (cdr lat)))))))
```

- `(firsts l)` 表示取出 list 中每一个子列表的第一个元素，来组成新列表，如 `(firsts '((a b) (c d) (e f))) => '(a c e)`

```scheme
(define firsts
  (lambda (l)
    (cond
     ((null? l) '())
     (else (cons (car (car l)) (firsts (cdr l)))))))
```

- `(insertR a b lat)` 表示把 atom a 插入到 lat 里 atom b 第一次出现的位置后，如 `(insertR 'a 'b '(c d b)) => '(c d b a)`

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

- `(subst a b lat)` 表示用 atom a 替换第一个 atom b，如 `(subst 'a 'b '(c b)) => '(c a)`

```scheme
(define subst
  (lambda (a b lat)
    (cond
     ((null? lat) '())
     ((eq? b (car lat)) (cons a (cdr lat)))
     (else (cons (car lat)
                 (subst a b (cdr lat)))))))
```

- `(subst2 a b c lat)` 表示用 atom a 替换 atom b 或第一个 atom c ，如 `(subst2 'a 'b '(c b)) => '(c a)`

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

# 多次操作的列表函数

- `(multirember a lat)` 表示删除 lat 中所有的 atom a

```scheme
(define multirember
  (lambda (a lat)
    (cond
     ((null? lat) '())
     ((eq? a (car lat)) (multirember a (cdr lat)))
     (else (cons (car lat)
                 (multirember a (cdr lat)))))))
```

- `(multiinsertR a b lat)` 表示在所有的 atom b 后面插入 atom a

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

- `(multiinsertR a b lat)` 表示在所有的 atom b 前面插入 atom a

```scheme
(define multiinsertL
  (lambda (a b lat)
    (cond
     ((null? lat) '())
     ((eq? b (car lat)) (cons a (cons b (multiinsertL a b (cdr lat))))) ; 注意这个地方
     (else (cons (car lat)
                 (multiinsertL a b (cdr lat)))))))
```

- `(multisubst a b lat)` 表示把所有的 atom b 替换成 atom a

```scheme
(define multisubst
  (lambda (a b lat)
    (cond
     ((null? lat) '())
     ((eq? b (car lat)) (cons a (multisubst a b (cdr lat))))
     (else (cons (car lat)
                 (multisubst a b (cdr lat)))))))
```
