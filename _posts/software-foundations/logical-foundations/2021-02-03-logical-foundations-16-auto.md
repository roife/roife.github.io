---
layout: "post"
title: "「SF-LF」 16 Auto"
subtitle: "More Automation"
author: "roife"
date: 2021-02-03

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

这一章将介绍更多的自动化 tactics，目的是简化这个 imp 的证明。

```coq
Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b evaluates to true *)
    apply IHE1. assumption.
  - (* b evaluates to false (contradiction) *)
    rewrite H in H5. discriminate.
  (* E_IfFalse *)
  - (* b evaluates to true (contradiction) *)
    rewrite H in H5. discriminate.
  - (* b evaluates to false *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
  - (* b evaluates to false *)
    reflexivity.
  - (* b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.
```

# `auto` Tactic

- `auto`
  : `auto` 可以自动搜索一些可以 `apply` 的前提，并且进行 `intros` & `apply`。使用 `auto` 不用担心它使证明误入歧途。要么它没解决问题，那么不改变当前的状态；要么直接解决了当前的 goal

```coq
Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.
```

由于搜索会花费很长时间，所以会对其搜索作出限制，默认为 `5`。当 `auto` 不能解决问题时，可以尝试扩大限制。

```coq
Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  auto. (* [auto 5] 不能解决问题 *)
  auto 6. (* 扩大限制后可以 *)
Qed.
```

## hint database

`auto` 证明时可以用一个 hint database，里面包括了一些相等和逻辑命题的 constructor 和 lemmas。

- `intro_auto`
  : 显示 `auto` 证明命题的过程

```coq
Example auto_example_5: 2 = 2.
Proof. info_auto. Qed.
(*
    (* info auto: *)
    simple apply @eq_refl (in core).
    No more subgoals.
*)

```

- `auto using ...`
  : 使用某个命题进行证明（即扩展 hint database）

```coq
Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. lia. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof. auto using le_antisym. Qed.
```

对于某些常用的命题可以添加到全局数据库中。

```coq
Hint Resolve T.         (* top-level theorem / constructor of an inductively defined proposition*)
Hint Constructors c.    (* 添加inductive definition 的所有 constructor *)
Hint Unfold d.          (* 学会对 [d] 进行 expand *)
```

## `Proof with t`

- `Proof with t`
  : 证明中的 `t1...` 等价于 `t1; t`

```coq
Theorem ceval_deterministic'_alt: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inversion E2; subst...
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *...
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H2. discriminate.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *...
Qed.
```

# Searching For Hypotheses

对于一种很常见的矛盾，不能用 `contradiction`，必须要 `rewrite H1 in H2; inversion H2`。

```coq
H1: beval st b = false
H2: beval st b = true
```

对于这种情况，可以用宏来实现。

## Ltac

- `Ltac macroName parameters... := tactics.`
  : 定义宏，并且用一套固定的 tactics 去解决

```coq
(* 定义宏 *)
Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.

Theorem ceval_deterministic'': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rwd H H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rwd H H5.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *)
      rwd H H2.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rwd H H4.
  - (* b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto. Qed.
```

## `match goal`

- `match goal`
  : 和 `Ltac` 一起用，让 coq 自动匹配对应的 hypothesis，`?x` 表示待绑定的变量或 hypothesis

和 `induction ;` 配合用可以直接解决大多数 case

```coq
Ltac find_rwd :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwd H1 H2
  end.

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
  end.

Theorem ceval_deterministic''''': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; try find_rwd;
    try find_eqn; auto.
Qed.
```

## `repeat`

在一些改动下，依然能复用这些宏。例如在语言中加入 `repeat...until...end` 语句。
此时颠倒一下自动化的顺序就能通过了。

```coq
Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (c : com) (b : bexp).

Notation "'repeat' x 'until' y 'end'" :=
         (CRepeat x y)
            (in custom com at level 0,
             x at level 99, y at level 99).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_RepeatEnd : forall st st' b c,
      st  =[ c ]=> st' ->
      beval st' b = true ->
      st  =[ repeat c until b end ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      st  =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ repeat c until b end ]=> st'' ->
      st  =[ repeat c until b end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; try find_rwd; try find_eqn; auto.
  - (* E_RepeatEnd *)
    + (* b evaluates to false (contradiction) *)
       find_rwd.
       (* oops: why didn't [find_rwd] solve this for us already?
          answer: we did things in the wrong order. *)
  - (* E_RepeatLoop *)
     + (* b evaluates to true (contradiction) *)
        find_rwd.
Qed.

Theorem ceval_deterministic': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; try find_eqn; try find_rwd; auto.
Qed.
```

但是这种情况比较 tricky，而且 debug 很麻烦。

# Tactics `eapply` and `eauto`

这两个 tactics 用来推迟量词的实例化。

## `eapply` tactic

```coq
Example ceval_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2). (* 不加 [with] 会提示 [Error: Unable to find an instance for the variable st'] *)
  - apply E_Ass. reflexivity.
  - apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.
```

例如这个证明中，`with` 后面的内容不加就不能进行 `apply`（因为这里是一个 quantified variable），但是在 `E_Ass` 可以直接推断出这个内容。所以我们可以 delay 给出 `with` 内容。

- `eapply`
  : 类似于 `apply`，但是可以推迟 instantiation of quantifiers

```coq
Example ceval'_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  eapply E_Seq. (* mentions the existential variable [?st'] *)
  - (* [ empty_st =[ X := 2 ]=> ?st' ] *)
    apply E_Ass. (* replaces ?st' with a new value contains a new existential variable [?n] *)
    (* [ aeval empty_st 2 = ?n ] *)
    reflexivity. (* [?n] is instantiated *)
  - (* [st'] has been replaced in subgoal 1 *) apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.
```

## `eauto` tactics

- `eauto`
  : 使用 `eapply` 代替 `apply` 的特殊 `auto`

- `info_eauto`
  : 类似 `info_auto`

```coq
(* 为了方便，先给一些 HINT *)
Hint Constructors ceval : core.
Hint Transparent state total_map : core.

Example eauto_example : exists s',
  (Y !-> 1 ; X !-> 2) =[
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  ]=> s'.
Proof. info_eauto. Qed.
```

注意，虽然 `eapply`/`eauto` 看起来很强大，但是它们很慢，所以不要随便使用。

# Constraints on Existential Variables

在证明中，所有 existential variables 的值都必须确定。

```coq
Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP. (* 提示 [All the remaining goals are on the shelf]，x 还不确定*)
Fail Qed. Abort.
```

另一个限制就是，加入一个 term 在某个 existential variable 后面创建了某个值，那么这个后面创建的值不能 instantiate 前面的 existential variables。例如下面的例子中，`HP` 可以 `destruct` 出 `HQ` 所需要的值，但是 `HP` 不能在 `HQ` 之后 `destruct`，需要换一下 `destruct` 和 `eapply` 的顺序。

```coq
Lemma silly2 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].
  Fail apply HP'.
Abort.

Lemma silly2_fixed : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.
```

注意在这里不能用 `assumption`，因为它不能处理 existential variables，需要用 `eassumption`（也可以直接用 `eauto`，`eauto` 包含了 `eassumption`）。

- `eassumption`
  : 类似于 `assumption`，能处理 existential variables

```coq
Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

(* use [eauto] *)
Lemma silly2_eauto : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eauto.
Qed.

```
