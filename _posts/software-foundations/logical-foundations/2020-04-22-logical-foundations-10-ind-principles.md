---
layout: "post"
title: "「SF-LF」 10 Ind Principles"
subtitle: "Induction Principles"
author: "roife"
date: 2020-04-22

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Basics

Coq 会为 `Inductive` 类型定义一个归纳规则。对于 `xxx`，其归纳法则为 `xxx_ind`。

``` coq
Check nat_ind.
(* ==> *)
nat_ind
     : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
```

`induction` tactic 可以看作是 `apply xxx_ind` 的包装，但是二者有细微区别：

- 使用归纳规则需要手动在 case 里进行 `intros`
- 使用归纳规则前一般不会 `intros` 归纳变量，因为 `apply` 要求命题和结论完全相同，如果 conclusion 中含有量词，那么当前也要保留量词

``` coq
Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
- (* n = O *) reflexivity.
- (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.  Qed.
```

对于 constructor `c t1 t2 ... a1 a2 ...`（其中 `ti` 为相应的类型，`ai` 为其它类型），归纳规则产生的命题为：

``` coq
(forall a1 a2 ...) (t1 t2 ... : T),
P t1 -> P t2 ->
... ->
forall tn, P tn ->
P (c t1 t2 ... a1 a2 ...).
```

对于不是递归定义的类型，可以用它证明某些命题对于所有情况都成立。

``` coq
t_ind : forall P : t -> Prop,
  ... case for c1 ... ->
  ... case for c2 ... -> ...
  ... case for cn ... ->
  forall n : t, P n
```

对于 polymorphic types，效果类似的：

``` coq
list_ind :
  forall (X : Type) (P : list X -> Prop),
     P [] ->
     (forall (x : X) (l : list X), P l -> P (x :: l)) ->
     forall l : list X, P l
```

# Induction hypotheses

归纳假设即蕴涵式的前提部分，使用时需要显式 `intros`。

``` coq
Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

(* 等价表述 *)
Definition P_m0r' : nat->Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
- (* n = O *) reflexivity.
- (* n = S n' *)
    intros n IHn. (* IHn 为归纳假设 *)
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.
```

# More on the `induction` Tactic

注意到用 `xxx_ind` 之前不能进行 `intros`，而 `induction` 会进行 `re-generalize`，所以可以先 `intros` 再 `induction`。

```coq
Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  (* [n] 被 re-generalize 了*)
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.
```

并且，对某个变量使用 `induction` 时，还会自动对前面的量词变量进行 `intros`。如 `Theorem plus_comm' : forall n m : nat, n + m = m + n.`，如果 `induction m`，则会自动对 `n` 进行 `intros`。

```coq
Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - (* n = O *) intros m. (* [m] 还没有被 intros*)
    rewrite <- plus_n_O. reflexivity.
  - (* n = S n' *) intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

Theorem plus_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  induction m as [| m']. (* [n] 已经被 intros 了 *)
  - (* m = O *) simpl. rewrite <- plus_n_O. reflexivity.
  - (* m = S m' *) simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.
```

# Induction Principles for Propositions

对于命题的归纳定义也会产生归纳规则。

```coq
Inductive ev'' : nat -> Prop :=
| ev_0 : ev'' 0
| ev_SS (n : nat) : ev'' n -> ev'' (S (S n)).

Check ev''_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, ev'' n -> P n -> P (S (S n))) ->
    forall n : nat, ev'' n -> P n.
```

并且，归纳命题的定义方式也会影响生成的归纳规则：

```coq
Inductive le1 : nat -> nat -> Prop :=
     | le1_n : forall n, le1 n n
     | le1_S : forall n m, (le1 n m) -> (le1 n (S m)).
Notation "m <=1 n" := (le1 m n) (at level 70).

(* 观察到每个规则都有一个变量 [n]，所以可以写出第二种规则。
   而且第二种生成的归纳规则形式上更简单 *)
Inductive le2 (n:nat) : nat -> Prop :=
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n (S m).
Notation "m <=2 n" := (le2 m n) (at level 70).

Check le1_ind :
  forall P : nat -> nat -> Prop,
    (forall n : nat, P n n) ->
    (forall n m : nat, n <=1 m -> P n m -> P n (S m)) ->
    forall n n0 : nat, n <=1 n0 -> P n n0.

Check le2_ind :
  forall (n : nat) (P : nat -> Prop),
    P n ->
    (forall m : nat, n <=2 m -> P m -> P (S m)) ->
    forall n0 : nat, n <=2 n0 -> P n0.
```

## Another Form of Induction Principles on Propositions

前面的 `ev''` 的 parameter 是 `n : nat`，除此之外还要加上一个 evidence 作为 parameter。

```coq
forall P : (forall n : nat, ev'' n -> Prop),
  P O ev_0 ->
  (forall (m : nat) (E : ev'' m),
    P m E -> P (S (S m)) (ev_SS m E)) ->
  forall (n : nat) (E : ev'' n), P n E
```

这种方式使得 evidence 也参与到了 proposition 中，而原来的方式（参数只有 `n`）更加方便和间接，实际上 Coq 生成的也是没有 evidence 的简化形式。

# Explicit Proof Objects for Induction

尽管用 proof tactics 来构建证明显得更加简单，但是对于一些特殊的证明会有些棘手，此时可以自己构建归纳规则。

```coq
Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

Print nat_ind.

(* response *)
nat_ind =
fun (P : nat -> Prop) (f : P 0) (f0 : forall n : nat, P n -> P (S n)) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | 0 => f
  | S n0 => f0 n0 (F n0)
  end
     : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n

Arguments nat_ind _%function_scope _ _%function_scope _%nat_scope

(** 一种更简洁的写法，用 [Fixpoint] *)
Fixpoint build_proof
         (P : nat -> Prop)
         (evPO : P 0)
         (evPS : forall n : nat, P n -> P (S n))
         (n : nat) : P n :=
  match n with
  | 0 => evPO
  | S k => evPS k (build_proof P evPO evPS k)
  end.

Definition nat_ind_tidy := build_proof.
```

例如对于 `evenb_ev` 的证明，由于普通的归纳规则是基于 `P(n) -> P(S n)`，在这个证明中会有的繁琐（偶数是 `P(S S n)`）。

- `induction ... using`：使用自定义归纳规则进行归纳

```coq
Definition nat_ind2 :
   forall (P : nat -> Prop),
   P 0 ->
   P 1 ->
   (forall n : nat, P n -> P (S(S n))) ->
   forall n : nat , P n :=
      fun P => fun P0 => fun P1 => fun PSS =>
         fix f (n:nat) := match n with
                            0 => P0
                          | 1 => P1
                          | S (S n') => PSS n' (f n')
                         end.

Lemma evenb_ev : forall n, evenb n = true -> ev'' n.
Proof.
 intros.
 induction n as [ | |n'] using nat_ind2.
 - apply ev_0.
 - simpl in H.
   inversion H.
 - simpl in H.
   apply ev_SS.
   apply IHn'.
   apply H.
Qed.
```
