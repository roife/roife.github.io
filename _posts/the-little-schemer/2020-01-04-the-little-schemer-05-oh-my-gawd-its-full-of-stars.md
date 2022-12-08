---
layout: "post"
title: "「The Little Schemer」 05 *Oh My Gawd* : It's Full of Stars"
subtitle: "list 嵌套"
author: "roife"
date: 2020-01-04

tags: ["The Little Schemer@读书笔记", "读书笔记@Tags", "Scheme@编程语言", "函数式编程@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 嵌套列表

从这里开始不仅仅讨论 lat，包括复合 list

- `(rember* a l)` 把 l 中所有 atom a 以及包含 a 的列表中的 a 删除

```scheme
(define rember*
  (lambda (a l)
    (cond
     ((null? l) '())
     ((atom? (car l))
      (cond
       ((eq? a (car l)) (rember* a (cdr l)))
       (else (cons (car l)
                   (rember* a (cdr l))))))
     (else (cons (rember* a (car l))
                 (rember* a (cdr l)))))))
```

注意对 `(car l)` 也要递归

- `(insertR* a b l)` 在 l 中所有的 atom b 后面加入 atom a

```scheme
(define insertR*
  (lambda (a b l)
    (cond
     ((null? l) '())
     ((atom? (car l))
      (cond
       ((eq? b (car l)) (cons b (cons a (insertR* a b (cdr l)))))
       (else (cons (car l) (insertR* a b (cdr l))))))
     (else (cons (insertR* a b (car l))
                 (insertR* a b (cdr l)))))))
```

- `(occur* a l)` l 中 atom a 出现的次数

```scheme
(define occur*
  (lambda (a l)
    (cond
     ((null? l) 0)
     ((atom? (car l))
      (cond
       ((eq? a (car l)) (add1 (occur* a (cdr l)))
        (else (add1 (occur* a (cdr l)))))))
     (else (o+ (occur* a (car l))
               (occur* a (cdr l)))))))
```

- `(subst* a b l)` 把 atom b 全部替换成 atom a

```scheme
(define subst*
  (lambda (a b l)
    (cond
     ((null? l) '())
     ((atom? (car l))
      (cond
       ((eq? b (car l)) (cons a (subst* a b (cdr l))))
       (else (cons (car l) (subst* a b (cdr l))))))
     (else (cons (subst* a b (car l))
                 (subst* a b (cdr l)))))))
```

- `(insertL* a b l)` 在 l 中所有的 atom b 前插入 atom a

```scheme
(define insertL*
  (lambda (a b l)
    (cond
     ((null? l) '())
     ((atom? (car l))
      (cond
       ((eq? b (car l)) (cons a (insertL* a b (cdr l))))
       (else (cons (car l) (insertL* a b (cdr l))))))
     (else (cons (insertL* a b (car l))
                 (insertL* a b (cdr l)))))))
```

- `(member* a l)` 询问 l 中是否包含 a

```scheme
(define member*
  (lambda (a l)
    (cond
     ((null? l) #f)
     ((atom? (car l))
      (cond
       ((eq? a (car l)) #t)
       (else (member* a (cdr l)))))
     (else (or (member* a (car l))
               (member* a (cdr l)))))))
```

- `(leftmost l)` 返回非空 S-expr 中最左边的 atom,

```scheme
(define leftmost
  (lambda (l)
    (cond
     ((atom? (car l)) (car l))
     (else (leftmost (car l))))))
```

注意这里约定 l 非空，则不需要处理 null list

- `and`、`or`、`cond` 都是短路的，且

```scheme
(and a b) => (cond (a b) (else #f))
(or a b) => (cond (a #t) (else b))
```

- `(eqlist? l1 l2)` 询问 list l1 与 list l2 是否相等

```scheme
(define eqlist?
  (lambda (l1 l2)
    (cond
     ((null? l1) (null? l2))
     ((null? l2) #f) ; 保证 l1 与 l2 都不是 null list
     ((atom? (car l1))
      (cond
       ((atom? (car l2)) (and (eqan? (car l1) (car l2))
                              (eqlist? (cdr l1) (cdr l2))))
       (else #f)))
     (else (and (eqlist? (car l1) (car l2))
                (eqlist? (cdr l1) (cdr l2)))))))
```

- `(equal? s1 s2)` 询问两个 S-expr 是否相等（要么是 atom、要么是 list）

```scheme
(define equal?
  (lambda (s1 s2)
    (cond
     ((and (atom? s1) (atom? s2)) (eqan? s1 s2))
     ((or (atom? s1) (atom? s2)) #f)
     (else (eqlist? s1 s2)))))
```

下面利用 equal? 重写 eqlist?（互相嵌套）

```scheme
(define eqlist?
  (lambda(l1 l2)
    (cond
     ((null? l1) (null? l2))
     ((null? l2) #f)
     (else (and (equal? (car l1) (car l2))
                (equal? (cdr l1) (cdr l2)))))))
```
