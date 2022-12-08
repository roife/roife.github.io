---
layout: "post"
title: "「SF-LF」 06 Logic"
subtitle: "Logic in Coq"
author: "roife"
date: 2020-03-29

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论", "C-H 同构@程序语言理论", "直觉主义@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Proposition

所有的命题都有 `Prop` 类型。

`Prop` 可以被赋值给定理声明（`Theorem`、`Lemma`、`Example`），也可以赋值给函数（`Definition`）。

``` coq
Definition plus_fact : Prop := 2 + 2 = 4.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.
```

通过 `Definition` 还可以生成带参数的命题，这种返回 `Prop` 的函数被称为定义了这些参数的 properties。

``` coq
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three. (*[nat -> Prop]*)
```

# Logical connectives

## conjunction

`and A B` 或 `A /\ B` 表示 A、B 皆为 true。

- `split`：将一个 conjunction 分解为多个 subgoals 分别证明

``` coq
Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
- apply HA.
- apply HB.
Qed.
```

当 hypotheses 是一个 conjunction 时，可以用 destruct 进行分解得到多个 hypotheses。

``` coq
Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(* 或者直接在 intros 的时候进行分解 *)
Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
```

conjunction 满足交换律与结合律。

``` coq
Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split.
  apply HP. apply HQ. apply HR.
Qed.
```

## disjunction

`or A B` 或 `A \/ B` 表示 A, B 至少有一个为 `true`。

可以用 `destruct` 来拆分一个 disjunction 的 hypotheses.

``` coq
Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H.
  destruct H as [Hn | Hm].
- rewrite Hn. reflexivity.
- rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(* 也可以直接用 intros 导入，此时会产生 subgoals *)
Lemma or_example' :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm]. (* [n = 0 \/ m = 0] *)
- rewrite Hn. reflexivity.
- rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.
```

要证明一个 disjunction, 可以用 `left` 和 `right` 两个 tactics 来挑选一方证明。注意使用 `left` 和 `right` 的时机也非常重要，提前使用可能推导不下去。（尤其是 hypotheses 和结论都有 or 时，一般先 destruct hypotheses）

``` coq
Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
- left. reflexivity.
- right. reflexivity.
Qed.
```

disjunction 满足交换律和结合律。

``` coq
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HA | HB].
- right. apply HA.
- left. apply HB.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
- intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
- intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.
```

## negation

根据 the principle of explosion，可以将否定命题定义为 `forall Q: P -> Q`，在 Coq 中则被定义为 `forall P: P -> False`，其中 `False` 是库中一个恒假的命题。

``` coq
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
```

对于 `False` 的 hypotheses，可以用 `destruct` 来用它结束证明。

``` coq
Theorem ex_falso_quodlibet : forall (P:Prop),
    False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.
```

可以用 negation 定义不等关系。

``` coq
Notation "x <> y" := (~(x = y)).
```

对于 `not`, 经常用 `unfold` 展开到 `False` 后，再利用 `apply in` 和 `destruct`。

``` coq
Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G. apply G in H.
  destruct H.
Qed.
```

证明不等关系时，通常先 `apply ex_falso_quodlibet` 转换为 `False`。

- exfalso
  : 类似于 `ex_falso_quodlibet`，将假命题转换为 `False` 后证明。

``` coq
Theorem not_true_is_false : forall b : bool,
    b <> true -> b = false.
Proof.
  intros [] H.
- (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet. apply H.
    reflexivity.
- (* b = false *)
    reflexivity.
Qed.
```

类似于 `False`，Coq 基础库还定义了 `True`。

``` coq
Lemma True_is_true : True.
Proof. apply I. Qed.
```

## iff

`iff P Q` 仅当 P 和 Q 相同时为真。

``` coq
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
```

``` coq
Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split. (* 因为是用 /\ 定义，因此可以用 split. *)
- (* -> *) apply HBA.
- (* <- *) apply HAB.
Qed.
```

引入 `From Coq Require Import Setoids.Setoid` 库后，当 `iff` 两端相同时可以用 `reflexivity` 和 `rewrite` 证明 `iff`。

也可以将一个 `iff` 命题 apply 到另一个命题上，Coq 会自动推导利用 `iff` 左边还是右边。

``` coq
Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
- apply mult_eq_0.
- apply or_example.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity. (* reflexivity *)
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H. (* apply *)
Qed.
```

## existential quantification

`exists n, P` 表示存在某个 `n` 使得 `P(n)` 成立，其中 `n` 被称为 `witness`。

证明特称命题时需要给出符合条件的值，然后证明此时命题成立。

``` coq
Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.
```

当特称命题是条件时，可以用 destruct 获得 witness 和 hypotheses，也可以直接用 intros 导入。

``` coq
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm]. (* implicit [destruct] *)
  exists (2 + m).
  apply Hm.  Qed.
```

# Define propositions recursively

``` coq
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]]. (* 注意这个 intros 的写法 *)
- exists 1. rewrite <- H. reflexivity.
- exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
- (* l = nil, contradiction *)
    simpl. intros []. (* 注意这里对于 False 直接用 intros 引入并分解 *)
- (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.
```

# proofs as functions

在 Coq 中，证明是 first-class objects，可以被当做函数使用。

``` coq
Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
- simpl in H. destruct H.
- discriminate Hl.
Qed.
(* 以下是四种使用方式 *)
(* [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(* [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(* Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(* Explicitly apply the lemma to a hypotheses. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H). (* 证明也可以和函数一样进行 type inference *)
Qed.
```

证明也有自己的类型。

``` coq
Check plus_comm.
(* ===> [forall n m : nat, n + m = m + n] *)
```

# Coq vs. Set Theory

A term in Coq is a member of at most one type.

``` example
集合论中 : n 属于一个由偶数组成的集合。
类型论中 : [even n] 成立，其中 even : nat -> Prop 描述了偶数的性质
```

## functional extensionality

可以定义两个函数之间的等价性，称为 `functional extensionality`。

``` coq
(forall x, f x = g x) -> f = g
```

`functional extensionality` 不是 Coq built-in 的部分，需要自行定义。

- `Axiom`：引入 Assumptions，为 Coq 内置类型系统添加规则，并且无需证明，但是要保证 Coq 的自洽性

``` coq
(* functional extensionality 与 Coq 内置系统自洽。*)
Axiom functional_extensionality : forall {X Y : Type}
                                    {f g : X -> T},
    (forall (x : X), f x = g x ) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.
```

- `Print Assumptions`：检查一个证明是否依赖于 Assumptions

``` coq
Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)
```

## booleans vs. propositions

一个结果为 `Bool` 的表达式与一个 `Prop` 等价，如 `evenb n = true <-> exists k, n = double k`。

``` coq
(* 转换 [evenb n = true] 和 [exists k, n = doubke k] *)
Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
- reflexivity.
- simpl. apply IHk'.
Qed.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  induction n as [| n' IHn'].
- simpl. exists 0. reflexivity.
- rewrite evenb_S. destruct (evenb n') eqn:E.
    + destruct IHn' as [x H]. exists x. rewrite <- H. reflexivity.
    + destruct IHn' as [x H]. rewrite -> H. exists (S x). reflexivity.
Qed.

Theorem even_bool_prop : forall n,
    evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
- intros H. destruct (evenb_double_conv n) as [k Hk]. (* 需要引用一个复杂的 Lemma *)
    rewrite Hk. rewrite H. exists k. reflexivity.
- intros [k Hk]. rewrite Hk. apply evenb_double. (* 引用的 Lemma 相对简单*)
Qed.
```

一般在推理中，`Prop` 用起来更方便。（比如 `a?=b = true` 和 `a = b`, 前者更难 rewrite）。但 `Prop` 不是 inductively 定义的，因此不可以被计算（not computational）。比如 `exists k, double k = 1000`。

有一种证明方法叫做 `Proof by Reflection`，即把 `Prop` 转换成 `Bool` 后，通过计算得到答案。

``` coq
Example even_1000 : exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed. (* 需要举出具体的值 *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed. (* 直接进行计算 *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed. (* Proof by Reflection *)
```

## Constructive logic

在 Coq 中排中律（`P \/ ~P`）是无法被证明的，除非转换成 `Bool` 曲线救国。（因为证明 disjunction 时只能使用 `left` / `right` tactic，而 P 属于哪种事先是不知道的）

``` coq
Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
- left. rewrite H. reflexivity.
- right. rewrite H. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.
```

在 Coq 中，如果要证明 `exists x, P x`，就必须构造出一个满足条件的 `x`，这种逻辑体系被称为`constructive logics`（与之对应的是 `classical logics`）。应用排中律能导出非 constructive logics，因此 Coq 中不能证明排中律，同样也不能使用反证法（`~ ~ P = P`）。

Constructive logics 可以让 Coq 写出 stronger claims，但是同时存在一部分命题无法证明。可以用 `Axiom` 向 Coq 中添加排中律，逻辑仍然自洽。

“排中律的否命题与 Coq 不一致”可以直接用 Coq 推导得到。（反过来不行）

``` coq
Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros P H. apply H. right. intros. apply H. left. apply H0.
Qed.
```

以下几条定律与排中律等价。

``` coq
Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).
```
