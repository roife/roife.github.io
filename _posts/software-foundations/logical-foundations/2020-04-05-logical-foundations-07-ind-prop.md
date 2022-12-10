---
layout: "post"
title: "「SF-LF」 07 Ind Prop"
subtitle: "Inductively Defined Propositions"
author: "roife"
date: 2020-04-05

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论", "正则表达式@形式语言", "形式语言@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# Inductively defined propositions

可以用几条 Rule 递归定义一个命题，如定义 evenness：

- Rule `ev_0`：`0` 是偶数
- Rule `ev_SS`：如果 `n` 是偶数，那么 `S (S n)` 也是偶数

之间的定义方法则是 `evenb n = true` 和 `exists k, n = double k`。

## Inference Rule & Proof Tree

Inference rules 是一种推理过程的写法，横线上方写 premises，横线下方写 conclusion，横线右边写规则名称。当横线上方没有 premises 时，说明 conclusion 恒成立。

如定义 evenness:

$$\dfrac {}{even\ 0} \tag{ev\_0}$$

$$\dfrac {even\ n} {even\ (S\ (S\ n))} \tag{ev\_SS}$$

类似的，inference rules 也可以连续书写，形成一棵 proof tree。

$$
\dfrac {} {
\dfrac {even\ 0} {
\dfrac {even\ 2} {
even\ 4
} \operatorname{(ev\_SS)}
} \operatorname{(ev\_0)}
}
$$

## Inductive definition

``` coq
Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

(* 或者可以写成 Theorem 的形式 *)
Inductive even' : nat -> Prop :=
| ev_0 : even 0
| ev_SS : forall n, even n -> even (S (S n)).
```

- even 的类型为 `nat -> Prop`，即 property of numbers. 其中 H 也被称为 `evidence`
- `nat` 定义出现在 `:` 右侧，称为 `index`; 而 polymorphic list 中的 `X : Type` 出现在 `:` 左侧，称为 `parameter`
  - 对于 parameter 而言，`list X` 表示一个泛型，它的所有 constructor 中的 X 都必须相同
  - 对于 index 而言，`even nat` 是一个 type family，其 constructor 的参数个数和类型都没有限制。同一个类型的 constructor 可以携带不同的 index，例如 `even 4 = ev_SS (ev_SS ev_0)`

``` coq
Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(* 类似函数的构造写法 *)
Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.
```

# Evidence

## Destruct on evidence

可以直接对 evidence 进行 `destruct`。类似于普通的 `Inductive` 类型，`destruct` 可以对 evidence 和 indices 的 constructor 分开讨论。

``` coq
Theorem ev_minus2 : forall n : nat,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EQN.
- (* EQN = ev_0 *) simpl. apply ev_0.
- (* EQN = ev_SS n' E' *) simpl. apply E'.
Qed.
```

但是在一些证明中 `destruct` 会失效，如：

``` coq
Theorem evSS_ev : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EQN.
- (* E = ev_0. *)
    (* 这里不能生成 assumptions, 因为 [destruct] 的作用是将 [S (S n)] 替换成另一个值，但是要证明的结论是里没有出现 [S (S n)] *)
Abort.

(* 可以手动改写 hypotheses, 写出 assumptions explicitly *)
Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
- (* E = ev_0 : even 0 *)
    left. reflexivity.
- (* E = ev_SS n' E' : even (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.
```

## Inversion on evidence

- `Inversion`：结合了 `destruct`、`discriminate`、`injection`、`intros`、`rewrite`，是一个综合的 tactic，可以看成一个特殊的 `destruct`。如果两边不同的 constructor 不同，说明可以 `discriminate`、`inversion` 会自动调用；如果 constructor 相同，说明可以 `injection`，`inversion` 会自动添加条件

``` coq
Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* [E = ev_SS n' E'] *)
- apply E'.
Qed.
```

## Induction on evidence

``` coq
Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
- (* E = ev_0 *)
    exists 0. reflexivity.
- (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.
```

注意 `E'` 和 `IH` 的区别，`E'` 是对 `E` 的归纳，`IH` 是对 conclusion 的归纳。

Induction on evidence 类似于对 `nat` 进行归纳。在 `nat` 中进行 `induction` 会讨论 `O` 和 `S n` 两种情况；在 `even` 中进行归纳则会讨论 `ev_0` 和 `ev_SS` 两种情况。二者本质是相同的

这里之所以要对 evidence 进行归纳而不是对 `nat` 进行归纳是因为这个性质并不是对所有的 `nat` 都成立，而是对满足命题的 `nat` 成立。

对 evidence 进行归纳是很常用的技巧，尤其在形式化程序语言中经常用到。

# Relations

`property` 只有一个参数，可以看做定义了一个满足 `property` 的子集；`relation` 有两个参数，可以看做定义了一个 `pair` 的子集。

``` coq
Inductive le : nat -> nat -> Prop :=
| le_n n : le n n
| le_S n m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n). (* 注意和之前的 <=? 的区别 *)
```

- `total_relation`：集合元素间两两有关系
- `empty_relation`：空关系

```coq
Inductive total_relation : nat -> nat -> Prop :=
  | tr : forall n m : nat, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop :=
  | er : forall n m : nat,  False -> empty_relation n m.
```

## 一些有用的函数

```coq
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o.
  intros E1 E2.
  generalize dependent E1.
  (*why can't induce on E1 *)
  induction E2.
  - intros. apply E1.
  - intros H. apply IHE2 in H. apply le_S in H. apply H.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n.
  - apply le_n.
  - apply le_S in IHn. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m.
  intro E.
  induction E.
  - apply le_n.
  - apply le_S in IHE. apply IHE.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m.
  intro E.
  inversion E.
  - apply le_n.
  - apply le_trans with (n := S n).
    + apply le_S. apply le_n.
    + apply H0.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction b.
  - rewrite <- plus_n_O. apply le_n.
  - rewrite <- plus_n_Sm. apply le_S. apply IHb.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.F
 unfold lt.
 intros.
 inversion H.
 - split.
   + rewrite <- plus_Sn_m. apply le_plus_l.
   + rewrite plus_n_Sm. rewrite plus_comm. apply le_plus_l.
 - rewrite H1. split.
    (* apply with is useful *)
   + apply le_trans with (n := S (n1+n2)).
     * rewrite <- plus_Sn_m. apply le_plus_l.
     * apply H.
   + apply le_trans with (n := S (n1+n2)).
    * rewrite plus_n_Sm. rewrite plus_comm. apply le_plus_l.
    * apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  intros n m.
  unfold lt.
  intro E.
  apply le_S.
  apply E.
Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent m.
  induction n.
  - intros. apply O_le_n.
  - intros. destruct m.
    + inversion H.
    + inversion H. apply n_le_m__Sn_le_Sm. apply IHn.
      apply H1.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - intros. inversion H. simpl. reflexivity.
  - intros. simpl. destruct n.
    + simpl. reflexivity.
    + simpl. apply IHm. apply Sn_le_Sm__n_le_m.  apply H.
Qed.

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros n m o.
  intros.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply leb_correct.
  apply le_trans with (n:=m).
  - apply H.
  - apply H0.
Qed.

Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  intros.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.
```

# Case Study

## Regular Expressions

### Syntax

``` coq
Inductive reg_exp {T : Type} : Type :=
| EmptySet
| EmptyStr
| Char (t : T)
| App (r1 r2 : reg_exp)
| Union (r1 r2 : reg_exp)
| Star (r : reg_exp).
```

### Matching Rules

$$ \dfrac {} {\texttt{[] =\textasciitilde{} EmptyStr}} \tag{MEmpty} $$

$$ \dfrac {} {\texttt{[x] =\textasciitilde{} Char x}} \tag{MChar}$$

$$ \dfrac {\texttt{$s_1$ =\textasciitilde{} $re_1$ $s_2$ =\textasciitilde{} $re_2$}} {\texttt{$s_1$ ++ $s_2$  =\textasciitilde{} App $s_1$ $s_2$}} \tag{MApp} $$

$$ \dfrac {\texttt{$s_1$ =\textasciitilde{} $re_1$}} {\texttt{$s_1$ =\textasciitilde{} Union $re_1$ $re_2$}} \tag{MUnionL} $$

$$ \dfrac {\texttt{$s_1$ =\textasciitilde{} $re_2$}} {\texttt{$s_1$ =\textasciitilde{} Union\ $re_1$ $re_2$}} \tag{MUnionR} $$

$$ \dfrac {} {\texttt{[] =\textasciitilde{} Star $re$}} \tag{MStar0} $$

$$ \dfrac {\texttt{$s_1$ =\textasciitilde{} $re_1$ \quad $s_2$ =\textasciitilde{} Star $re$}} {\texttt{$s_1$ ++ $s_2$ =\textasciitilde{} Star $re$}} \tag{MStarApp} $$

``` coq
Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar x : exp_match [x] (Char x)
| MApp s1 re1 s2 re2
       (H1 : exp_match s1 re1)
       (H2 : exp_match s2 re2) :
    exp_match (s1 ++ s2) (App re1 re2)
| MUnionL s1 re1 re2
          (H1 : exp_match s1 re1) :
    exp_match s1 (Union re1 re2)
| MUnionR re1 s2 re2
          (H2 : exp_match s2 re2) :
    exp_match s2 (Union re1 re2)
| MStar0 re : exp_match [] (Star re)
| MStarApp s1 s2 re
           (H1 : exp_match s1 re)
           (H2 : exp_match s2 (Star re)) :
    exp_match (s1 ++ s2) (Star re).
```

### remember tactic

使用 `induction` 时可能会丢失一些信息，导致证明无法继续进行。比如 `s1 =~ Star re` 经过 `induction`会得到 7 个 subgoals，但是实际上只有 `MStar0` 和 `MStarApp` 满足条件。（因为把 `Star re` 看做一个整体）

- `remember`：记忆某些信息防止在 `induction` 时丢失

``` coq
Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
    s1 =~ Star re ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
- (* MEmpty *)  discriminate.
- (* MChar *)   discriminate.
- (* MApp *)    discriminate.
- (* MUnionL *) discriminate.
- (* MUnionR *) discriminate.
- (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.
- (* MStarApp *) (* 此时会产生一个等价于 remember 产生的 hypotheses *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.
```

### Pumping Lemma

> `Pumping Lemma`：对于足够长的字符串 s 和一个匹配的正则表达式 re，将其一个子串重复（pump）n 遍后，得到的新字符串仍然能匹配 re。

``` coq
Fixpoint pumping_constant {T} (re : @reg_exp T) : nat := (* 定义"足够长"为字符串长度大于正则表达式的长度 *)
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
    pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
    pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T := (* 定义一个重复字符串的函数和相关 Lemma *)
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
    napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
- reflexivity.
- simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= Poly.length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Import Coq.omega.Omega.
(* an important but simple lemma *)
(* ref: https://firobe.fr:3000/Firobe/Coq/src/master/IndProp.v *)
Lemma inequ_plus : forall (a b n m : nat),
  a + b <= n + m ->
  a <= n \/ b <= m.
Proof.
  intros a b n m.
  omega.
Qed.
Lemma inequ_plus2 : forall (a b n : nat),
  a + b <= n ->
  a <= n.
Proof.
  intros a b n.
  omega.
Qed.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  -  (* MChar *)
    simpl. omega.
  -  (* MApp *)
    rewrite app_length. simpl. intro. apply inequ_plus in H. inversion H.
    + apply IH1 in H0. inversion H0. inversion H1. inversion H2. inversion H3.
    exists x. exists x0. exists (x1 ++ s2). split.
      * rewrite H4. rewrite <- app_assoc.  rewrite <- app_assoc. reflexivity.
      * split. inversion H5.
        { apply H6. }
        { intros m. replace (x ++ napp m x0 ++ x1 ++ s2) with ((x ++ napp m x0 ++ x1) ++ s2).
          { apply MApp. inversion H5. apply H7. apply Hmatch2. }
          { rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. } }
    + apply IH2 in H0. inversion H0. inversion H1. inversion H2. inversion H3.
    exists (s1++x). exists x0. exists x1. split.
      * rewrite H4. rewrite <- app_assoc. reflexivity.
      * split. inversion H5.
        { apply H6. }
        { intros m. replace ((s1 ++ x) ++ napp m x0 ++ x1) with (s1 ++ (x ++ napp m x0 ++ x1)).
          { apply MApp. apply Hmatch1. inversion H5. apply H7. }
          { rewrite <- app_assoc. reflexivity. } }
  - (* MUnionL *)
    simpl. intros. apply inequ_plus2 in H.
    intros. apply IH in H. inversion H. inversion H0. inversion H1.  inversion H2.
    exists x. exists x0. exists x1. split.
    { inversion H3. reflexivity. }
    { destruct H4 as [H41 H42]. split. apply H41. intro m. apply MUnionL. apply H42. }
  - (* MUnionR *)
    simpl. intros. rewrite plus_comm in H. apply inequ_plus2 in H.
    intros. apply IH in H. inversion H. inversion H0. inversion H1.  inversion H2.
    exists x. exists x0. exists x1. split.
    { inversion H3. reflexivity. }
    { destruct H4 as [H41 H42]. split. apply H41. intro m. apply MUnionR. apply H42. }
  - (* MStar0 *)
    simpl. omega.
  - (* MStarApp *)
    simpl. simpl in IH2. rewrite app_length. intros.
    assert (1 <= Poly.length s1 \/ 1 <= Poly.length s2). { omega. }
    inversion H0.
    + exists []. exists s1. exists s2. split. simpl. reflexivity. split.
      * unfold not. intros. apply f_equal with (f:=Poly.length) in H2. simpl in H2. rewrite H2 in H1. inversion H1.
      * intro m. simpl. induction m.
        { simpl. apply Hmatch2. }
        { simpl. rewrite <- app_assoc. apply MStarApp. apply Hmatch1. apply IHm. }
    + apply IH2 in H1. inversion H1 as [x [x0 [x1 [H2 [H3 H4]]]]].
      exists (s1 ++ x). exists x0. exists x1. split.
      * rewrite <- app_assoc. rewrite H2. reflexivity.
      * split. apply H3. intro m. rewrite <- app_assoc. apply MStarApp.
        { apply Hmatch1. }
        { apply H4. }
Qed.
```

## Reflection

利用 reflection 可以将 `Prop` 和一个 `Bool` 绑定（一般是和与之对应的 `Bool` 绑定），并利用两个 `Theorem` 进行轻松转化，方便证明。

``` coq
Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.
```

``` coq
(* iff 与 reflect 互相转化 *)
Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
- apply ReflectT. rewrite H. reflexivity.
- apply ReflectF. rewrite H. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. split.
- intros HP. destruct H.
    + reflexivity.
    + apply H in HP. destruct HP.
- intros Hb. rewrite Hb in H. inversion H. apply H0.
Qed.
```

``` coq
(* 一个使用例子 *)
Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
    filter (fun x => n =? x) l <> [] ->
    In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
- (* l = [] *)
    simpl. intros H. apply H. reflexivity.
- (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H]. (* 注意此处 destruct 直接将对应的命题转换为 [P] 和 [~P] 两种形式 *)
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.
```

`Reflect` 能大大缩短证明长度，并且因 Coq 的 `SSReflect (small-scale reflection)` 库开始流行，这个库证明了许多数学定理。

## Pigeonhole Principle

即鸽巢定理。这里的表述方式为：设 $l_2$ 是鸽巢编号，$l_1$ 是个体选择鸽巢的编号，若 $l_1$ 中的所有元素都在 $l_2$ 中，且 $l_1$ 数量大于 $l_2$，则 $l_1$ 内必有重复元素。

```coq
Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros.
  induction l.
  - inversion H.
  - destruct H.
    + exists nil. exists l.
      rewrite <- H. reflexivity.
    + apply IHl in H.
      destruct H as [l1 [l2 H]].
      exists (x0::l1). exists l2.
      rewrite -> H. reflexivity.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats_new : forall h l , In h l -> repeats (h::l)
  | repeats_old : forall h l , repeats l -> repeats (h::l).

Lemma in_app_comm : forall (X:Type) (x:X) (l1 l2:list X),
  In x (l1++l2) -> In x (l2++l1).
Proof.
  intros.
  rewrite In_app_iff.
  rewrite In_app_iff in H.
  inversion H.
  - right. apply H0.
  - left. apply H0.
Qed.

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
  excluded_middle ->
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros X l1. induction l1 as [|x l1' IHl1'].
  - intros l2 Excluded_Middle H2 H3. inversion H3.
  - intros l2 Excluded_Middle H2 H3. destruct (Excluded_Middle (In x l1')).
    + apply repeats_new. apply H.
    + apply repeats_old. destruct (in_split X x l2).
      * apply H2. simpl. left. reflexivity.
      (* need to designate a l2 for IHl1' *)
      * destruct H0. apply (IHl1' (x0++x1)).
        apply Excluded_Middle. }
        { intros.
          assert (In x2 l2). { apply H2. simpl. right. assumption. }
          rewrite H0 in H2. apply in_app_comm with (x:=x2) in H2.
          destruct (Excluded_Middle (x = x2)).
          { rewrite H5 in H. apply H in H1. inversion H1. }
          { rewrite H0 in H4. simpl. rewrite In_app_iff in H4. inversion H4.
            { rewrite In_app_iff. left. assumption. }
            { simpl in H6. inversion H6.
              { apply H5 in H7. inversion H7. }
              { rewrite In_app_iff. right. assumption. }
            }
          }
          { simpl. right. assumption. }
        }
        { rewrite H0 in H3. rewrite app_length. rewrite app_length in H3. simpl in H3.
          unfold lt. unfold lt in H3.
          rewrite plus_n_Sm. apply Sn_le_Sm__n_le_m in H3.
          assumption.
        }
Qed.
```

## Verified RE matcher

[Regular-expression derivatives reexamined - JFP 09](http://people.cs.uchicago.edu/~jhr/papers/2009/jfp-re-derivatives.pdf)

### 预备

首先引入一些预备性的内容。

```coq
Require Export Coq.Strings.Ascii.
Definition string := list ascii.

Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. inversion H0.
Qed.
```

还可以证明几个简单的 Lemmas。

```coq
(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.
```

### app

```coq
(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1]. *)
(* 非常关键的一步 *)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  split.
  {
    intros. apply app_exists in H.
    destruct H as [s0 [s1 [eq1 [eq2 eq3]]]].
    destruct s0.
    - left. split. apply eq2. simpl in eq1. rewrite eq1. apply eq3.
    - right. inversion eq1. exists s0. exists s1. split. reflexivity. split. apply eq2. apply eq3.
  }
  {
    intros [[H1 H2]|[s0 [s1 [H1 [H2 H3]]]]].
    - assert (a::s = [] ++ a::s).
      {simpl. reflexivity. }
      rewrite H. apply MApp.
      apply H1. apply H2.
    - rewrite H1.
      assert(a::s0++s1=([a]++s0)++s1).
      {simpl. reflexivity. }
      rewrite H. apply MApp.
      + simpl. apply H2.
      + apply H3.
  }
Qed.
```

### union

```coq
(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H2.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.
```

### star

```coq
(** [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re].  *)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  intros.
  split.
  {
    intros. remember (a::s) as s'. remember (Star re) as re'. induction H.
    - inversion Heqre'.
    - inversion Heqs'.
    - inversion Heqre'. destruct s1.
      + simpl in Heqs'. apply IHexp_match2 in Heqs'.
        inversion Heqs' as [s0 [s1 Heqs]]. exists s0. exists s1. rewrite <- H2. rewrite <- H2 in Heqs. apply Heqs.
        apply Heqre'.
      + inversion Heqs'. exists s1. exists s2. split.
        * reflexivity.
        * split. rewrite H3 in H. rewrite H2 in H. apply H.  rewrite H2 in H0. apply H0.
   }
   {
    intros. inversion H as [s0 [s1 [H0 [H1 H2]]]].
    rewrite H0. simpl. assert (a::s0++s1=(a::s0)++s1).
    - simpl. reflexivity.
    - rewrite H3. apply MStarApp.
      + apply H1.
      + apply H2.
   }
Qed.
```

### `matches_eps`

```coq
(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : @reg_exp ascii, reflect ([ ] =~ re) (m re).

(** It tests if a given regex matches the empty string: *)
Fixpoint match_eps (re: @reg_exp ascii) : bool := match re with
  | EmptyStr => true
  | Star _ => true
  | App re1 re2 => (match_eps re1) && (match_eps re2)
  | Union re1 re2 => (match_eps re1) || (match_eps re2)
  | _ => false
  end.

(** Prove that [match_eps] indeed tests if a given regex matches the empty string. *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  induction re.
  - apply ReflectF. apply empty_is_empty.
  - apply ReflectT. apply MEmpty.
  - apply ReflectF. intro. inversion H.
  - apply iff_reflect. simpl. rewrite andb_true_iff.
    apply reflect_iff in IHre1. apply reflect_iff in IHre2. split.
    + intros. inversion H.
      assert (s1=[]). { destruct s1. reflexivity. inversion H0. }
      rewrite H5 in H0. simpl in H0.
      rewrite H0 in H4. apply IHre2 in H4. rewrite H5 in H3. apply IHre1 in H3.
      split. assumption. assumption.
    + intros. inversion H. apply IHre1 in H0. apply IHre2 in H1.
      apply app_exists. exists []. exists [].
      split. simpl. reflexivity. split. assumption. assumption.
  - apply iff_reflect. simpl. rewrite orb_true_iff.
    apply reflect_iff in IHre1. apply reflect_iff in IHre2. split.
    + intros. inversion H.
      * left. apply IHre1 in H2. assumption.
      * right. apply IHre2 in H2. assumption.
    + intros. apply union_disj. inversion H.
      * left. apply IHre1 in H0. assumption.
      * right. apply IHre2 in H0. assumption.
  - apply iff_reflect. simpl. split.
    + intros. reflexivity.
    + intros. apply MStar0.
Qed.

 (** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition beq_ascii x y :=
  if ascii_dec x y then true else false.

Lemma beq_ascii_true_iff : forall a b,
  beq_ascii a b = true <-> a = b.
Proof.
    intros x y.
    unfold beq_ascii.
    destruct (ascii_dec x y) as [|Hs].
    - subst. split. reflexivity. reflexivity.
    - split.
      + intros contra. inversion contra.
      + intros H. inversion H. subst. destruct Hs. reflexivity.
Qed.

Lemma beq_ascii_false_iff : forall a b,
  beq_ascii a b = false <-> a <> b.
Proof. intros x y. rewrite <- beq_ascii_true_iff.
  rewrite not_true_iff_false. reflexivity.
Qed.
```

### derive

```coq
Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, optional (derive)  *)
(** Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | Char b => if beq_ascii a b then EmptyStr else EmptySet
  | EmptyStr => EmptySet
  | Union r1 r2 => Union (derive a r1) (derive a r2)
  | App r1 r2 => if (match_eps r1) then Union (derive a r2) (App (derive a r1) r2)
                 else App (derive a r1) r2
  | Star r => App (derive a r) (Star r)
  end.

(** Prove that [derive] in fact always derives strings. *)
Lemma derive_corr : derives derive.
Proof.
  unfold derives.
  intros a re.
  generalize dependent a.
  induction re.
  - intros. unfold is_der. intros. split.
    + intros. inversion H. + intros. inversion H.
  - intros. unfold is_der. intros. split.
    + intros. inversion H. + intros. inversion H.
  - intros. unfold is_der. intros. split.
    + intros. destruct (beq_ascii a t) eqn:eq.
      * simpl. rewrite eq. inversion H. apply MEmpty.
      * rewrite beq_ascii_false_iff in eq. inversion H. apply eq in H3. inversion H3.
    + intros. unfold derive in H. destruct (beq_ascii a t) eqn:eq.
      * inversion H. rewrite beq_ascii_true_iff in eq. rewrite eq. apply MChar.
      * inversion H.
  - intros. unfold is_der. unfold is_der in IHre1. unfold is_der in IHre2. split.
    + intros. apply app_ne in H.  destruct H as [[H1 H2]|[s0 [s1 [H1 [H2 H3]]]]].
      * rewrite (reflect_iff _ (match_eps re1)) in H1.
        { simpl. rewrite H1. apply MUnionL.  apply IHre2 in H2.  apply H2. }
        { simpl. apply match_eps_refl.  }
      * rewrite H1. destruct (match_eps re1) eqn:eq.
        { simpl. rewrite eq. apply MUnionR. apply MApp. apply IHre1 in H2. apply H2. apply H3. }
        { simpl. rewrite eq. apply MApp. apply IHre1 in H2. apply H2. apply H3. }
    + simpl. destruct (match_eps re1) eqn:eq.
      * intros. apply union_disj in H. inversion H.
        { apply app_ne. apply IHre2 in H0. left.
          split. apply (reflect_iff _ (match_eps re1)). apply match_eps_refl. apply eq. apply H0. }
        { apply app_exists in H0. destruct H0 as [s0 [s1 [H1 [H2 H3]]]]. rewrite H1.
          assert (a::s0++s1=(a::s0)++s1). simpl. reflexivity.
          rewrite H0. apply MApp. apply IHre1 in H2. apply H2. apply H3.
        }
      * intros. apply app_exists in H. destruct H as [s0 [s1 [H1 [H2 H3]]]].
        rewrite H1.
        assert (a::s0++s1=(a::s0)++s1). simpl. reflexivity.
        rewrite H. apply MApp. apply IHre1 in H2. apply H2. apply H3.
  - intros. unfold is_der. unfold is_der in IHre1. unfold is_der in IHre2. split.
    + intros. apply union_disj in H. inversion H.
      * simpl. apply MUnionL. apply IHre1 in H0. assumption.
      * simpl. apply MUnionR. apply IHre2 in H0. assumption.
    + intros. simpl in H. apply union_disj in H. inversion H.
      * apply MUnionL. apply IHre1 in H0. assumption.
      * apply MUnionR. apply IHre2 in H0. assumption.
  - intros. unfold is_der. unfold is_der in IHre. split.
    + intros. apply star_ne in H. destruct H as [s0 [s1 [H1 [H2 H3]]]].
      simpl. rewrite H1. apply MApp.
      * apply IHre in H2. apply H2.
      * apply H3.
    + intros. simpl in H. apply app_exists in H. destruct H as [s0 [s1 [H1 [H2 H3]]]].
      rewrite H1. assert (a::s0++s1=(a::s0)++s1). simpl. reflexivity. rewrite H. apply MStarApp.
      * apply IHre in H2. apply H2.
      * apply H3.
Qed.
```

### matcher

最后，我们用定义一个正则表达式匹配器。

```coq
(* 如果一个函数是正则表达式的匹配器，那么对于任何匹配正则表达式的字符串，都能被这个函数接收 *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool :=
  match s with
  | [] => match_eps re
  | h::t => regex_match t (derive h re)
  end.

(** Finally, prove that [regex_match] in fact matches regexes. *)
Theorem regex_refl : matches_regex regex_match.
Proof.
  unfold matches_regex. intros.
  generalize dependent re.
  induction s.
  - intros. apply iff_reflect. split.
    + intros. rewrite (reflect_iff _ (match_eps re)) in H.
      * apply H.
      * apply match_eps_refl.
    + intros. simpl in H. rewrite (reflect_iff _ (match_eps re)).
      * apply H.
      * apply match_eps_refl.
  - intros. apply iff_reflect. split.
    + simpl. intros. apply (derive_corr x re) in H.  specialize (IHs (derive x re)).
      apply reflect_iff in IHs. apply IHs. apply H.
    + simpl. intros. apply (derive_corr x re). specialize (IHs (derive x re)).
      apply reflect_iff in IHs. apply IHs. apply H.
Qed.
```
