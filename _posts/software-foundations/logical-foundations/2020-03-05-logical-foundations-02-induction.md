---
layout: "post"
title: "「SF-LF」 02 Induction"
subtitle: "Proof by Induction"
author: "roife"
date: 2020-03-05

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Basic

- `replace (a) with (b)`：将 a 替换为 b，同时多出一个证明 a 的 subgoal

``` coq
Theorem plus_swap' : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc. rewrite plus_assoc.
  replace (n + m) with (m + n).
  reflexivity.
- rewrite plus_comm. reflexivity.
Qed.
```

- `assert (a). {}`：声明一个局部命题 a，并在 `{}` 中给出证明

``` coq
Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.
```

# Induction

利用归纳法证明命题。类似于 `destruct`，将命题分为两个部分。

- 证明 `P(0)` 成立
- 假设 `P(n')` 成立（`IHn'` 成立），将 `P(n)` 中的 `n` 替换成 `n'`，利用 `P(n')` 证明 `P(n)` 成立

``` coq
Theorem plus_n_O : forall n : nat,
    n = n + 0.
Proof.
  intros n. induction n as [|n' IHn']. (*intros 可忽略，但是不建议忽略*)
- reflexivity.
- simpl. rewrite <- IHn'. reflexivity.
Qed.
```

# Commutativity & Associativity & Distributivity

## 加法交换律

``` coq
Lemma plus_n_O : forall n : nat,
    n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.

Lemma plus_n_Sm : forall n m : nat, (*将 S 整体与第二个加数化简，实用*)
    S (n + m) = n + S m.
Proof.
  intros n m.
  induction n as [|n' IHn'].
- reflexivity.
- simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IHn'].
- rewrite -> plus_n_O. reflexivity.
- simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.
```

## 加法结合律

``` coq
Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n IHn'].
- reflexivity.
- simpl. rewrite <- IHn'. reflexivity.
Qed.
```

注意：`(n + m) + p` 与 `n + m + p` 等价。

## 乘法交换律

``` coq
Lemma plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n). { rewrite -> plus_comm. reflexivity. } rewrite -> H.
  rewrite -> plus_assoc. reflexivity.
Qed.

Lemma mult_n_Sm : forall m n : nat,
    n * (S m) = n + n * m.
Proof.
  intros n m. induction m.
- reflexivity.
- simpl. rewrite -> IHm. rewrite -> plus_swap. reflexivity.
Qed.

Theorem multi_comm : forall m n : nat,
    m * n = n * m.
Proof.
  intros m n. induction m.
- rewrite -> mult_0_r. reflexivity.
- rewrite -> mult_n_Sm. simpl. rewrite -> IHm. reflexivity.
Qed.
```

## 乘法分配律

``` coq
Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [|n' IHn'].
- reflexivity.
- simpl. rewrite IHn'. rewrite -> plus_assoc. reflexivity.
Qed.
```

## 乘法结合律

``` coq
Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
- reflexivity.
- simpl. rewrite -> mult_plus_distr_r. rewrite -> IHn'. reflexivity.
Qed.
```
