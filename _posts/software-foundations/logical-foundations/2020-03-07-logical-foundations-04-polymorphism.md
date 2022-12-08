---
layout: "post"
title: "「SF-LF」 04 Polymorphism"
subtitle: "Polymorphism, Higher-Order Functions and Church numerals"
author: "roife"
date: 2020-03-07

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论", "Church 数@函数式编程"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Polymorphism

## Polymorphic Lists

利用 Polymorphism 将 list 与任意类型绑定。

``` coq
Inductive list(X : Type) : Type :=
| nil
| cons (x : X) (l : list X).
```

使用时 nil 和 cons 也要加上类型，如 `(cons nat 3 (nil nat))`。

- list 可以被看作一个 `Type -> Inductive` 的函数，或者是一个 `Type -> Type` 的函数
- nil 的类型为 `forall X : Type, list X`
- cons 的类型为 `forall X : Type, X -> list X -> list X`

``` coq
(* Polymorphic function *)
Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.
```

在 polymorphisc lists 上面使用 `destruct` 和 `induction` 时，不需要带类型参数。

## Type Annotation Inference & Arguments Synthesis

使用 Polymorphism 时可以让 Coq 自动进行类型推导。

``` coq
Fixpoint repeat' X x count : list X := (* 自动推导出 X x count 三个参数的类型 *)
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.
```

可以用 `_` 占位，让 Coq 根据上下文类型信息自动推导所填参数，这样就可以避免重复写类型参数。

``` coq
Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).
```

实际上 Type Annotation Inference 和 Type Arguments Synthesis 使用同一个过程来完成推导。

## Implicit Arguments & Explicit Arguments

- `Arguments`：定义隐式参数

用大括号包裹的参数会变成 Impilicit 参数，使用时被赋予默认值，不能再显式给出。

使用时部分参数可以用 `_` 替代。

``` coq
Arguments nil {X}. (* 此时 nil 的类型变换 list ?X *)
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
```

也可以在定义函数时直接用大括号定义 Implicit 参数。

``` coq
Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
```

但是 Inductive 类型不能这么定义。（因为 Inductive 类型在定义变量时必须提供类型参数）

有些情况下需要为 Implicit 参数显式提供参数，此时可以用 `@` 前置修饰函数。

``` coq
Fail Definition mynil := nil. (* Fail 表示语句会执行失败*)
Definition mynil' := @nil nat.

(*这里也可以用另一种写法让 Coq 进行类型推导*)
Definition mynil'' : list nat = nil.
```

## Polymorphic Pairs

Polymorphic pairs 也被称为 products。

``` coq
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
```

同样可以定义类型之间的 product，即 product types。注意 `(x, y)` 是一个值，而 `X*Y` 是一种类型，即 `(x, y) : X*Y`。

``` coq
Notation "X * Y" := (prod X Y) : type_scope.
(* type_scope 表明这个定义只接受类型参数，防止和乘法搞混 *)
```

用同样的方法可以定义 `fst` 和 `snd` 函数。

``` coq
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.
```

`Combine`（或者通常叫 zip）用 list X 和 list Y 生成一个 `list X * Y` 的列表。

``` coq
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* 同样可以定义 unzip *)
Definition app_list_pair {X Y : Type} (lp1 : (list X) * (list Y)) (lp2 : (list X) * (list Y)) :
  (list X) * (list Y) :=
  (app (fst lp1) (fst lp2), app (snd lp1) (snd lp2)).

Fixpoint split {X Y : Type} (l : list (X * Y)) :
  (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (h1, h2)::t => app_list_pair ([h1] [h2]) (split t)
  end.
```

## Polymorphic Options

``` coq
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.
```

# Functions as Data

Coq treats functions as first-class citizens.

## Higher-order functions

即操作函数的函数。

``` coq
Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(* @doit3times 的类型为 (X -> X) -> X -> X *)
```

## anonymous functions

- `fun params => body`：匿名函数

``` coq
Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.
```

## filter

filter 是一个 higher-order function，接受一个 predicate（`X -> bool`）并且将一个 list 中满足 predicate 的元素筛选出来，返回一个新的 list。即 `filter pred l = [x | x in l && (pred x)]`。

``` coq
Fixpoint filter {X : Type} (test : X -> bool) (l : list X)
: (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: filter test t
            else filter test t
  end.
```

``` coq
(* filter 的一个应用：根据 predicate 分割 list *)
Definition partition {X : Type}
           (test : X -> bool)
           (l : list X)
: list X * list X :=
  (filter test l, filter (fun x => (negb (test x)))  l).
```

## map

`map` 也是一个 higher-order function，接受一个函数并将其作用到 list 中所有的函数上。即 `map f [n1, n2, ...,] = [f n1, f n2, ...]`。

``` coq
Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.
```

`map` 不仅可以作用于 list，还可以定义作用于 option 的 list。

``` coq
Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.
```

## fold

`fold` 也是一个威力强大的 higher-order function，把 f 作用在列表中的所有元素和一个初始值上：`fold f [n1, n2, ...] b = f(n1 f(n2 f(... f(nk b)))))`

``` coq
Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
: Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.
```

## construct functions

函数也可以返回另一个函数。

每个多参数函数都可以看作是“返回函数”的函数（Currying）。如 `plus` 的类型为 `nat -> nat -> nat`，可以看作 `nat -> (nat -> nat)`。

``` coq
Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
```

相对也有 Uncurrying。

对于 Currying 而言，`A -> B -> C` 被解释为 `A -> (B -> C)`。对于 Uncurrying 而言，`A -> B -> C` 被解释为 `(A * B) -> C`。

``` coq
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).
```

# Church numerals

Church numerals 是一种用函数嵌套来表示自然数的方法。（所有的数字都是函数！)

``` coq
Definition cnat := forall X : Type, (X -> X) -> X -> X.

(* 函数的嵌套层数表示数字的大小 *)
Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(* 注意，cnat 是一个函数，它接受三个参数，分别是类型，构造函数 f, 和零元 x *)
```

相应的运算非常巧妙。

``` coq
Definition succ (n : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => m X f (n X f x).

Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) => m X (n X f).
(* 即 [fun (X : Type) (f : X -> X) (x : X) => m X (n X f) x.] *)

Definition exp (n m : cnat) : cnat :=
  fun (X : Type) => m (X -> X) (n X).
(* 即 [fun (X : Type) (f : X -> X) (x : X) => (m (X -> X) (n X) f) x.] *)
(* 想象一棵 [m] 层的树，每个节点有 [n] 个叶子节点，那么第 [m] 层就是答案 *)
```