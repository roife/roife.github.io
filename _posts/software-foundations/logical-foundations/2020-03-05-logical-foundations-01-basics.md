---
layout: "post"
title: "「SF-LF」 01 Basics"
subtitle: "Functional Programming in Coq"
author: "roife"
date: 2020-03-05

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Grammar

所有的语句都必须用 `.` 来结尾。

- `Inductive`：定义递归类型

``` coq
Inductive bool : Type :=
| true
| false.
```

可以定义复合递归类型。

``` coq
Inductive rgb : Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p: rgb).
(*primary red 是 color 类型*)
```

也可以定义 Tuple

``` coq
Inductive nybble : Type :=
| bits (b0 b1 b2 b3 : bit).
```

- `Definition`：定义函数

``` coq
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => false
  | true b2
  end.

Definition isred(c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false (*_ 是占位符*)
  end.

Definition pred(n : nat) : nat :=
  match n with
  | O => O
  | S n' => n' (*pattern matching*)
  end.
```

- `Compute`：计算函数

``` coq
Compute (andb true false).
```

- `Example`：定理

类似的还有 `Theorem`、`Lemma`、`Fact`、`Remark`。

``` coq
Example test_andb: (andb (andb true true) false) = false.
Proof. simpl. reflexivity. Qed.
```

- `Notation`：定义运算符

``` coq
Notation "x && y" := (andb x y).

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope
(*定义优先级，结合性和 scope*)
(*scope 也可以用 % 标明，如 O%nat 表示 nat 下的 O*)
```

- `Admitted`：表示定理可以直接使用。（用作占位符）

``` coq
Admitted.
```

- `Check`：输出语句的类型

``` coq
Check andb. (*[bool -> bool]*)
(*[bool -> bool -> bool] 表示 andb 接受两个 bool，返回 bool*)
```

- `Module`：modole 中的元素要通过 `module.foo` 来访问

``` coq
Module NatPlayground.

end.
```

- `Fixpoint`：递归函数

``` coq
Fixpoint evenb(n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.
```

# Tactics

Proof 和 Qed 之间的证明部分被称为 Tactics。

- `simpl`：化简等号两边，便于改进证明
- `reflexivity`：化简并验证是否成立
- `intros`：引入变量/函数/条件等
- `rewrite`：使用条件重写命题

``` coq
Theorem plus_id_example : forall n m : nat,
    n = m ->
    n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H. (*rewrite from left to right*)
  reflexivity.
Qed.
```

- `destructive`：按照归纳定义分类讨论

``` coq
Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  (*将 n 按照归纳定义，分成零元参数与一元参数，分别讨论*)
  (*eqn:E 会让每次要讨论的情况用 E 表示，便于查看*)
- reflexivity.
    (*每种情况分类，也可以用 + * {} 来标注情况的嵌套*)
Qed.
```

分类的过程可以直接在 intros 中完成：`intros [|n]`。

对于 `intros [|]` 可以直接写 `intros []`。

# Nat

## 自然数定义

``` coq
Inductive nat : Type :=
| O
| S (n : nat).
(*S (S (S O)) = 3*)
```

## 加法/乘法定义

``` coq
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint mult (n : nat) (m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (multi n' m)
  end.
```

## 减法定义

``` coq
Fixpoint minus (n : nat) (m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.
```

## 比较运算符定义

``` coq
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
    match m with
    | O => false
    | S m' => leb n' m'
    end
  end.
```

# contradictory in case analysis

有些时候分类讨论会出现这种情况：当前讨论与条件矛盾，此时应该结束讨论。（后面可以直接用 `discriminate` 这个 tactic）

这里用了一个小技巧，使得遇到矛盾的条件时能够停止讨论。

``` coq
Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros [] [].
- reflexivity. (*true true*)
- simpl. intros H. rewrite H. reflexivity. (*true false, 不满足条件，先 intros H 得到 true=false, 然后 rewrite 结束讨论*)
- simpl. reflexivity.
- simpl. intros H. rewrite H. reflexivity.
Qed.
```

# Fixpoint and Structural Recursion

Coq 要求递归时必须有某些项在递减，以使得递归能够结束。Coq 不一定能判别出某些递减项（停机问题），此时可能会让证明有一些 unnatural。
