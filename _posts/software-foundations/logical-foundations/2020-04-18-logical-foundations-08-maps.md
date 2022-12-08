---
layout: "post"
title: "「SF-LF」 08 Maps"
subtitle: "Total and Partial Maps"
author: "roife"
date: 2020-04-18

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# map

map（即 dictionary）包括两类：

- total maps：找不到元素时会返回一个默认值
- partial maps：返回一个 `option` 类型，找不到元素时返回 None

**Map 其实就是一个函数。**

# Standard Lib in Coq

- `Require`：使用成员时要加限定名
- `Import`：可以直接使用成员

# Identifiers

在 Lists 曾中定义了 `id` 作为 identifiers，但接下来都会使用标准库中的 `string` 作为 identifiers。

``` coq
(* 定义两个 string 是否相等 *)
(* string_dec 的类型为 [{x=y} + {x<>y}], 即 [sumbool] 类型，可以看作是带 evidence 的 [bool] 类型 *)
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof. intros s. unfold eqb_string. destruct (string_dec s s) as [|Hs].
- reflexivity.
- destruct Hs. reflexivity.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs. destruct Hs. reflexivity.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.
```

# Total maps

下面会用函数来定义 map，两个返回值相同的函数会被视为相同的 map，此时值被存放在 closure 中。首先定义 total map 类型。

``` coq
Definition total_map (A : Type) := string -> A.
```

## Definition

``` coq
(* 定义空 map *)
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

(* 更新 map 中的值 *)
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

(* 用运算符简化语法 *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).
Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).
```

## Lemmas

``` coq
Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  intros A x v.
  unfold t_empty.
  reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros A m x v. unfold t_update. rewrite <- eqb_string_refl. reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H. unfold t_update.
  rewrite <- eqb_string_false_iff in H. rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold t_update. apply functional_extensionality.
  intros x0. destruct (eqb_string x x0).
  reflexivity. reflexivity.
Qed.

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros x y.
  destruct (eqb_string x y) eqn:E.
- apply ReflectT. apply eqb_string_true_iff. apply E.
- apply ReflectF. apply eqb_string_false_iff. apply E.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros A m x. unfold t_update. apply functional_extensionality.
  intros x0. destruct (eqb_stringP x x0).
  rewrite e. reflexivity. reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 H. unfold t_update. apply functional_extensionality.
  intros x. destruct (eqb_stringP x1 x).
- rewrite <- e. rewrite <- eqb_string_false_iff in H. rewrite H. reflexivity.
- reflexivity.
Qed.
```

# Partial maps

partial maps 可以在 total maps 的基础上定义。

``` coq
Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).
```

类似可以定义 Partial maps 的 lemmas。
