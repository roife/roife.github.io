---
layout: "post"
title: "「The Little Schemer」 02 Do It, Do It Again, and Again, and Again..."
subtitle: "基本函数"
author: "roife"
date: 2020-01-03

tags: ["The Little Schemer@读书笔记", "读书笔记@Tags", "Scheme@编程语言", "函数式编程@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 列表

- `(car l)` 表示取出 list 的第一个元素，结果可以是 atom 也可以是 list，如 `(car '((a b c) x y z)) => '(a b c)`
- `(cdr l)` 表示取出 list 里除了第一个元素的剩下部分，如 `(cdr '((a b c) x y z)) => '(x y z)`，当 list 只有一个元素时返回 `()`

`car` 与 `cdr` 都不可对 atom 或者 null list 操作

- `(cons x l)` 表示把一个元素加到另一个 list 的头部，返回一个 list，如 `(cons 'a (car '((b) c d))) => '(a b)`，第一个参数随意，第二个参数必须是 list

可以用 `(cons atom '())` 构建一个表 `'(atom)`

- `(null? l)` 表示判断 list 是否为 null，如 `(null? '(a)) => #f`，参数必须是 list

```scheme
(define atom?
  (lambda (x)
    (and (not (pair? x))
         (not (null? x)))))
```

- `(eq? a b)` 表示判断两个 atom 是否相等，如 `(eq? 'a 'a) => #`，参数必须是非数字的 atom，不可以是 list
- `(lat? lat)` 表示判断一个 list 全部都是由 atom 组成，如 `(lat? '(a b (c))) => #f`，对于 null list 也返回 `#t`

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
