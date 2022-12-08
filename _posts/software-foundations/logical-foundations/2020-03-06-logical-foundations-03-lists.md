---
layout: "post"
title: "「SF-LF」 03 Lists"
subtitle: "Working with Structured Data"
author: "roife"
date: 2020-03-06

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Pairs

## Definition

``` coq
Inductive natprod : Type :=
| pair (n1 n2 : nat).
```

## 定义基本运算

``` coq
(*frist element*)
Definition fst(p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
(*second element*)
Definition snd(p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
(*swap pair*)
Definition swap_pair(p : natprod) : nat :=
  match p with
  | pair x y => pair y x
  end.

Notation "(x, y)" := (pair x y). (*定义表示方法*)
```

注意：模式匹配中的“多匹配”与 pair 匹配本质不同（如 "2 3" 与 "(2, 3)" 不同）。

## destruct

证明时可以用 `destruct` 暴露 pair 内部元素。注意：这个操作不会产生 subgoal，与 nat 中的分类讨论不相同。

``` coq
Theorem surjective_pairing : forall (p : natprod),
    p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. (*pair 被分解为两个元素*)
  reflexivity.
Qed.
```

# Lists of numbers

## Definition

``` coq
Inductive natlist : Type :=
| nil
| cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
(* 第三种定义意为把 n 元 Notation 转换为二元 constructor *)
(** Definition mylist1 := 1 :: (2 :: (3 :: nil)).
    Definition mylist2 := 1 :: 2 :: 3 :: nil.
    Definition mylist3 := [1;2;3].*)
```

## 一些函数

``` coq
(* 返回列表长度 *)
Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* 连接两个列表 *)
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).

(* 返回头部和尾部 *)
Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
```

# destruct and induction in lists

## destruct

``` coq
Theorem tl_length_pred : forall l:natlist,
    pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
- reflexivity.
Qed.
```

## induction

``` coq
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
- reflexivity.
- simpl. rewrite -> IHl1'. reflexivity.  Qed.
```

注意：`::` 运算符和 `++` 运算的优先级相同，二者都是右结合。

# reversing lists

``` coq
Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.
```

一些有用的 Lemma.

``` coq
(* 对合性 *)
Lemma rev_involutive : forall l : natlist,
    rev (rev l) = l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
- reflexivity.
- simpl. rewrite rev_app_distr. simpl. rewrite IHl'. reflexivity.
Qed.

(* 利用对合性的巧妙证明 *)
Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. intros H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.
```

# natoption

``` coq
Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.
```

# if

- if cond then exp1 else exp2

选择语句

``` coq
Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if n =? O then Some a
               else nth_error' l' (pred n)
  end.
```

由于 coq 没有 `bool` 类型，因此二元归纳类型可以用作 cond 语句的判定。当返回值为归纳类型的第一个 constructor 时，等价于 `true`；第二个 constructor 等价于 `false`。

# partial map

## id

``` coq
Inductive id : Type :=
  | Id (n : nat).
```

``` coq
Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  destruct x as [n].
- simpl. rewrite <- eqb_refl. reflexivity.
Qed.
```

## dictionary

``` coq
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

```

``` coq
(* 通过覆盖来更新 key *)
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.
(* 查找 *)
Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.
```

``` coq
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl. rewrite <- eqb_id_refl. reflexivity.
Qed.
```
