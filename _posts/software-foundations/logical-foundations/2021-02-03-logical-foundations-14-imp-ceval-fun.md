---
layout: "post"
title: "「SF-LF」 14 ImpCEvalFun"
subtitle: "An Evaluation Function For Imp"
author: "roife"
date: 2021-02-03

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

在 `IMP` 一章中我们看到 Relational Definition 比 Functional Definition 的好处，这一章尝试用 Functional Definition 来定义 IMP。

# A Broken Evaluator

回顾之前的方法。

```coq
Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | <{ skip }> ⇒
        st
    | <{ l := a1 }> ⇒
        (l !-> aeval st a1 ; st)
    | <{ c1 ; c2 }> ⇒
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | <{ if b then c1 else c2 end }> ⇒
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | <{ while b1 do c1 end }> ⇒
        if (beval st b1) then
          ceval_step1 st <{ c1; while b1 do c1 end }>
        else st
  end.
```

# A Step-Indexed Evaluator

一个 terminate 的方法就是增加步数限制。

注意，这里的 `i` 表示语句嵌套深度（顺序/条件/循环）。

为了指明这个程序是运行完成还是因为嵌套过深而终止，返回值可以用一个 `optional` 类型指明。

```coq
(* 一个简易的 optional 类型 *)
Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN (* 如果执行成功则继续 *)
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i' (* 深度增加 *)
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1) (* 循环条件成立 *)
          then LETOPT st' <== ceval_step st c1 i' IN (* 执行一次 *)
               ceval_step st' c i' (* 再次执行循环 *)
          else Some st
    end
  end.
```

一个程序的例子：

```coq
Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.
```

# Relational vs. Step-Indexed Evaluation

下面证明，在有穷步骤内，`ceval_step` 与原来的运算是等价的。

## $\rightarrow$

```coq
Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].
  - (* i = 0 -- contradictory *)
    intros c st st' H. discriminate H.
  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* skip *) apply E_Skip.
      + (* := *) apply E_Ass. reflexivity.

      + (* ; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Evaluation of r1 terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        * (* Otherwise -- contradiction *)
          discriminate H1.

      + (* if *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      + (* while *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. simpl in H1. assumption. }
         { (* r1 = None *) discriminate H1. }
        * (* r = false *)
          injection H1 as H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr.
Qed.
```

## Lemma `ceval_step_more`

```coq
Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    + (* skip *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* := *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        discriminate Hceval.

    + (* if *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.

    + (* while *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. discriminate Hceval.
Qed.
```

## $\leftarrow$

```coq
Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  - exists 1. simpl. reflexivity.
  - exists 1. simpl. rewrite H. reflexivity.
  - inversion IHHce1 as [i1 E1]. inversion IHHce2 as [i2 E2].
    destruct (i1 <=? i2) eqn:IE.
    + apply leb_complete in IE.
      apply (ceval_step_more _ _ _ _ _ IE) in E1.
      exists (S i2). simpl. rewrite E1. apply E2.
    + apply leb_complete_conv in IE.
      assert(IE' : i2 <= i1). { lia. }
      apply (ceval_step_more _ _ _ _ _ IE') in E2.
      exists (S i1). simpl. rewrite E1. apply E2.
  - inversion IHHce as [i E]. exists (S i).
    simpl. rewrite H. apply E.
  - inversion IHHce as [i E]. exists (S i).
    simpl. rewrite H. apply E.
  - exists 1. simpl. rewrite H. reflexivity.
  - inversion IHHce1 as [i1 E1]. inversion IHHce2 as [i2 E2].
    destruct (i1 <=? i2) eqn:IE.
    + apply leb_complete in IE.
      apply (ceval_step_more _ _ _ _ _ IE) in E1.
      exists (S i2). simpl. rewrite H. rewrite E1. apply E2.
    + apply leb_complete_conv in IE.
      assert(IE' : i2 <= i1). { lia. }
      apply (ceval_step_more _ _ _ _ _ IE') in E2.
      exists (S i1). simpl. rewrite H. rewrite E1. apply E2.
Qed.
```

## $\leftrightarrow$

```coq
Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.
```

# Determinism of Evaluation Again

通过上面的定理，可以更简单的证明 Determinism of Evaluation。

```coq
Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  lia. lia.  Qed.
```
