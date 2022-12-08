---
layout: "post"
title: "「SF-LF」 11 Rel"
subtitle: "Properties of Relations"
author: "roife"
date: 2021-01-30

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# Relations

在 Coq 中，集合 $X$ 上的二元关系是一组参数为两个的命题。

```coq
Definition relation (X: Type) := X -> X -> Prop.

Print le. (* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.
```

# Basic Properties

## Partial Functions

在集合 $X$ 上的关系 $R$，如果对于每一个 $x$，至多只有一个 $y$ 使得 $R\ x\ y$，则 $R$ 是一个部分函数。

```coq
Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.
```

`next_nat` 是一个部分函数。

```coq
Print next_nat.
(* ====> Inductive next_nat (n : nat) : nat -> Prop :=
           nn : next_nat n (S n) *)
Check next_nat : relation nat.

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed.
```

`<=` 不是部分函数（证明思路：假设是部分函数，由于 $0 \le 0$ 且 $0 \le 1$ 则 $0 = 1$，矛盾）。

```coq
(* [<=] 不是部分函数 *)
Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense.   Qed.
```

## Reflexive Relations

即自反性，$\forall x \in X, R\ x\ x$。

```coq
Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.
```

`<=` 是自反的。

```coq
Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.  Qed.
```

## Transitive Relations

即传递性，$\forall a, b, c \in X, R\ a\ b \rightarrow R\ b\ c \rightarrow R\ a\ c$。

```coq
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
```

`<=` 是传递的。

```coq
Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo.  Qed.
```

### 一个有用的定理

```coq
Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.
```

## Symmetric and Antisymmetric Relations

即对称与反对称：
- Symmetric: $\forall a, b \in X, R\ a\ b \rightarrow R\ b\ a$
- Antisymmetric: $\forall a, b \in X, R\ a\ b \rightarrow R\ b\ a \rightarrow a = b$

```coq
Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.
```

`le` 是非对称的，而且是反对称的。

```coq
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold not.
  unfold symmetric.
  intros.
  assert (1 <= 0). {
    apply H. apply le_S. apply le_n.
  }
  inversion H0.
Qed.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros.
  inversion H.
  - reflexivity.
  - rewrite <- H2 in H0. assert (S m <= m). {
    apply le_trans with (a).
    + apply H0.
    + apply H1.
  }
  apply le_Sn_n in H3.
  inversion H3.
Qed.
```

## Equivalence Relations

即等价关系。

```coq
Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).
```

## Partial Orders

即偏序。

```coq
Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).
```

`<=` 是偏序关系。

```coq
Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans.  Qed.
```

## Preorders

即严格偏序。

如果集合内所有元素可比较则称为全序。

```coq
Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).
```

# Reflexive, Transitive Closure

即自反且传递的闭包。

```coq
(* 直观定义 *)
Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step x y (H : R x y) : clos_refl_trans R x y
    | rt_refl x : clos_refl_trans R x x
    | rt_trans x y z
          (Hxy : clos_refl_trans R x y)
          (Hyz : clos_refl_trans R y z) :
          clos_refl_trans R x z.

(* 更好用的定义 *)
Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.
```

例如 `next_nat` 的对称传递闭包就是 `le`。

```coq
Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.
```

下面证明上面两种自反传递闭包的定义等价。

```coq
Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl.   Qed.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros.
  induction H.
  - apply H0.
  - apply rt1n_trans with y.
    + apply H.
    + apply IHclos_refl_trans_1n. apply H0.
Qed.

Theorem rtc_rsc_coincide :
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros. split.
  - intros. induction H.
    + apply rsc_R. apply H.
    + apply rt1n_refl.
    + apply rsc_trans with y.
      * apply IHclos_refl_trans1.
      * apply IHclos_refl_trans2.
  - intros. induction H.
    + apply rt_refl.
    + apply rt_trans with y.
      * apply rt_step. apply H.
      * apply IHclos_refl_trans_1n.
Qed.
```
