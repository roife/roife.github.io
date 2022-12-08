---
layout: "post"
title: "「SF-LF」 05 Tactics"
subtitle: "More Basic Tactics"
author: "roife"
date: 2020-03-15

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# apply

- `apply`：应用 hypotheses/lemmas，用于倒推

如果已知命题没有条件，且已知命题与目标命题一致，此时可以用 apply。类似于 `rewrite <- eq. reflexivity.`。

一般在目标命题与已知命题的结论相同时使用，此时只需要证明已知命题的条件成立。如 `A->B` 应用了 `B`，那么 `A` 成为一个 subgoal。

使用 `apply` 时如果遇到全称量词，那么 Coq 会自动匹配变量。

``` coq
Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.
```

- `symmetry`：交换等号两边

`apply` 要求已知命题必须和目标命题一模一样，如等号两边不能交换方向，否则要用 `symmetry`。

``` coq
Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5)  ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  apply H.  Qed.
```

- `apply with`：`apply` 无法自动匹配变量时，进行手动变量匹配

``` coq
Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]). (* 此处可以直接写 [c;d], coq 能自动推断出是 m 要手动赋值*)
  apply eq1. apply eq2.
Qed.
```

# `injection`

用 `Inductive` 定义的类型实际上包含了两个事实，单射性与互斥性。

- injective: `if S n=S m, then n=m.`
- disjoint: `forall n, O <> S n.`

``` coq
(* 单射性证明 *)
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. } (* 通用证明方法：引入 constructor 的反函数 *)
  rewrite H2. rewrite H1. reflexivity.
Qed.
```

- `injective`：利用单射性得出新条件

``` coq
Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H. (* 此时多出一个由单射性得到的等式 *)
  intros Hnm. apply Hnm.
Qed.
(* 一次得出多个等式 *)
Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.
```

- `injective as`：得出新等式的同时命名

``` coq
Theorem injection_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.
```

单射性的逆命题对 constructor 和函数均成立。

``` coq
Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq. reflexivity.
Qed.
```

# discriminate

利用 `Inductive` 的互斥性可以得到，当命题的两个不同的 constructor 被等号连接时，命题错误，此时可以退出证明。

- `discriminate`：利用互斥性，当条件命题不成立时退出证明

``` coq
Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
- (* n = 0 *)
    intros H. reflexivity.
- (* n = S n' *)
    simpl.
    intros H. discriminate H. (* 分类条件不成立 *)
Qed.
```

`discriminate` 也用于条件不成立或矛盾时，推出任何命题，即 `forall P, false -> P`，这也被称作 `principle of explosion`。

# using tactics on hypotheses (in)

通常 tactics 都是作用在目标命题上，通过 `in` 可以让其作用在 hypotheses 上。如 `apply L in H`、`simpl in H`。

``` coq
Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b  ->
     n =? m = b.
Proof.
  intros n m b H.
  simpl in H. apply H.
Qed.
```

但是 `apply in` 有些特别。

- `apply in`：在 hypotheses 上用另一个 hypotheses/lemma, 常用于正推。（和 apply 恰好相反）

如 `P : A->B` 应用了命题 A（`apply P in A`）。那么 `P` 就会转变为命题 `B`。

# generalize dependent

使用 `induction` 时会产生一个命题 `P(n')` 用于辅助命题 `P(n)` 的证明。在多变量命题 `P(n, m)` 中对 n 进行 `induction`，变量 `intros` 的顺序会影响到 `P(n', m)` 的表述。

当变量没有被 `intros` 时，变量在命题中以 `forall` 的形式存在，此时 `apply` 和 `rewrite` 可以用 `P(n, m)` 证明 `P(n, m')`，更加通用；反之 `intros` 后，变量变成了一个具体的数值，而不在是通识符，无法实现这种证明。

如 `forall m : nat, (n =? m) = true -> n = m` 可以证明 `(n =? m') = true -> n = m'`，而 `(n =? m) = true -> n = m` 则无法推出。

因此使用 `induction` 时需要注意变量 `intros` 的时刻，在 `induction` 之前 `intros` 会导致 `P(n', m)` 丧失通用性。

尤其是这种情况：`P(n, m) -/> P(S n, m)` 且 `P(n, m) -> P(S n, S m)`。此时如果同时 `intros n m`，会得到条件 `P(S n, m)` 和 `P(n, S m)`，这对证明是没有帮助的。但是如果只 `intros n`，就可以得到 `forall m, P(n, m)`。

``` coq
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn']. (* [forall m : nat, (n =? m) = true -> n = m] *)
- destruct m as [| m' IHm'].
    + reflexivity.
    + discriminate.
- intros m H.
    destruct m as [| m' IHm'].
    + discriminate.
    + apply IHn' in H. apply f_equal. apply H.
Qed.
```

- `generalize dependent`：generalize 变量

由于 Coq `intros` 变量时是按照变量出现顺序进行的，因此可能会出现一个 generalize 的变量不得不被 `intros`，此时可以用 `generalize dependent` 进行 generalize。

``` coq
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| x XH IHx].
- simpl. reflexivity.
- intros n. intros H.
    simpl. simpl in H.
    destruct n as [| n'] eqn:E1.
    + simpl. discriminate.
    + simpl. apply IHx. injection H as H'. apply H'.
Qed.
```

# unfold

- `unfold`：展开定义

`simpl`、`reflexivity`、`apply` 有时候也会自动 `unfold`，但是 `unfold` 更明确。

``` coq
Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.
```

遇到 `match` 时 `unfold` 有可能出现分支的情况，此时可以 `destruct`。

``` coq
Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
(* 出现分支 [
  match m with
  | 0 => 5
  | S _ => 5
  end + 1 = match m + 1 with
            | 0 => 5
            | S _ => 5
            end + 1
]*)

  destruct m eqn:E.
- reflexivity.
Qed.
```

# destruct

当对 Inductive 类型使用 `destruct`，会根据 Inductive 中定义的 contructor 进行分类讨论。或展开函数时对 match 的情况进行匹配。还可以对于一个表达式使用 `destruct`。（本质上是对 match 匹配）

``` coq
(* 对 match 匹配 *)
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| n l' IHn'].
- simpl. intros l1 l2 H. injection H as H1 H2. rewrite <- H1. rewrite <- H2. reflexivity.
- intros l1 l2 H. simpl in H.
    destruct n as [x y]. destruct (split l') as [lx ly].
    injection H as H1 H2. rewrite <- H1. rewrite <- H2.
    simpl. rewrite IHn'. reflexivity.
    reflexivity.
Qed.
```

``` coq
(* 对条件匹配 *)
Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) reflexivity.
Qed.
```

`eqn` 用于记录 `desturct` 的情况，可以被省略，但 `destruct` 条件时通常保留以记录信息。

``` coq
Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else false.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity. (* 若没有记录 Heqe3 则无法 rewrite *)
    - (* e3 = false *) discriminate eq.  Qed.
```
