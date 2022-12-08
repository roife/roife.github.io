---
layout: "post"
title: "「SF-LF」 12 Imp"
subtitle: "Simple Imperative Programs"
author: "roife"
date: 2021-01-31

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论", "解释器@编译", "编译@Tags", "未完成@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

这一章开始尝试用 Coq 写一个解释性语言。

```
Z := X;
Y := 1;
while ~(Z = 0) do
  Y := Y * Z;
  Z := Z - 1
end
```

# Arithmetic and Boolean Expressions

## Abstract Syntax

```coq
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
```

## Evaluation

```coq
Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.
```

## Optimization

考虑一个优化：`(APlus (ANum 0) e) => e`。

```coq
Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.
```

下面证明这个优化的正确性。

```coq
Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.
```

# Coq Automation

## Tacticals

Tacticals 是一种 high-order tactics，可以将其他 tactics 作为参数。

### `try` tactic

- `try T`
  : T 是一个 tactic，如果成功了就使用，否则不做任何事。在实际证明中不会用到，但是在自动化证明中可能会用到。

```coq
Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* Just [reflexivity] would have failed. *)
  apply HP. (* We can still finish the proof in some other way. *)
Qed.
```

### `T;T'` tactic

- `T;T'`
  : 先执行 `T`，然后在 `T` 产生的每一个 subgoal 上执行 `T'`

```coq
Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* [destruct] the current goal *)
  destruct n; simpl; reflexivity.
Qed.
```

`;` 可以和 `try` 结合使用，大幅简化证明。

```coq
Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... but the remaining cases -- ANum and APlus -- are different: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* special case *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.   Qed.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.
```

通常在 `induction` 之类的后可以用 `...; try ...` 省略一堆证明。

#### General Formal `T; [T1 | T2 | ... | Tn]`

`T; [T1 | T2 | ... | Tn]` 表示先使用 `T`，然后对第 i 个 subgoal 使用 `Ti`。

`T; T'` 是一种特殊形式，表示 `T; [T' | T' | T' |...]`。

### `repeat` tactic

`repeat` 会重复执行 tactics 直到执行失败。

对于某些不会失败的 tactics（如 `repeat simpl`），当形式不再改变时才会停下来。


```coq
Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.
```

如果某个 tactics 不会失败，而且每次都会改变形式（比如循环 `rewrite`，那 coq 就会死循环）。

```coq
Theorem repeat_loop : forall (m n : nat),
    m + n = n + m.
Proof
  intros m n.
  (* 死循环 *)
  repeat rewrite Nat.add_comm.
  (* In Proof General, [C-c C-c] will break out of the loop. *)
Admitted.
```

这种死循环说明证明失败了，并不意味着构建了错误的证明。

### 简化证明

利用这三个 tactics 可以大幅简化证明。

```coq
Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue       => b
  | BFalse      => b
  | BEq a1 a2   => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2   => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1     => BNot (optimize_0plus_b b1)
  | BAnd b1 b2  => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.


Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros.
  induction b; repeat (try (simpl; repeat(try(rewrite optimize_0plus_sound));reflexivity)).
  - simpl. rewrite IHb. reflexivity.
  - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.
```

## Defining New Tactic Notations

- `Tactic Notation`
  : 定义新的 tactic 组合现有 tactics

```coq
Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.
```

用 Coq 内置的 `Ltac` 语言可以在更大程度上对 tactics 进行定制，但是比较复杂。还可以用 OCaml 来对底层进口定制，但是很少用。

## `omega` tactic

`omega` 使用 Omega（William Pugh [Pugh 1991]）算法，可以解决 Presburger arithmetic 的问题。对于 Presburger arithmetic 问题，如果用 Omega 算法失败了，说明问题错误，或者本身不是一个 Presburger arithmetic 问题。

- Presburger Arithmetic
  + 数字常量，加法（`+` 或 `S`），减法（`-` 或 `pred`），乘法
  + 相等关系（`=` 或 `<>`），偏序关系（`<=`）
  + 逻辑运算（`/\`，`\/`，`~`，`->`）

```coq
Example plus_comm__omega : forall m n,
    m + n = n + m.
Proof.
  (* 需要 [From Coq Require Import Lia] *)
  intros. lia.
Qed.
```

## A Few More Handy Tactics

- `clear H`
  : 从上下文删除 hypothesis `H`
- `subst H`
  : 对于变量 `x`，找到一个 `x = e` 或 `e = x` 形式的 assumption，并进行替换，删除这个 assumption
- `subst`
  : 对于所有变量执行 `subst` 操作
- `rename x into y`
  : 将所有 `x` 重命名为 `y`
- `assumption`
  : 从上下文找一个 hypothesis 形式和当前 goal 相同，并解决这个 goal
- `contradiction`
  : 从上下文找一个 hypothesis，其在逻辑上是 false 的，并解决这个 goal
- `constructor c`
  : 从当前环境的 `Inductive` 中找一个可以用于当前 goal 的 constructor `c`，并执行 `apply c`

# Evaluation as a Relation

Evaluation 可以看作“表达式”和“值”之间的一个 relation，所以可以用 relation 的形式定义 evaluation。

```coq
(* 为了方便起见写出 hypothesis 的名称 *)
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

(* 还可以简化 notations *)
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMult e1 e2) ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.
```

## Inference Rule Notation

可以将这种关系写成 Inference Rules 的形式。

$$
\dfrac {}{\operatorname{\mathtt{ANum}}\ n \Longrightarrow n} \tag{E\_ANum}
$$

$$
\dfrac
{e_1 \Longrightarrow n_1, e_2 \Longrightarrow n_2}
{\operatorname{\mathtt{APlus}}\ e_1\ e_2 \Longrightarrow n_1 - n_2}
\tag{E\_APlus}
$$

如果一个语句内有多个变量，可以考虑适当 `generalize dependent`。

## Equivalence of the Definitions

可以证明 relation 和 functional 的形式是等价的。

```coq
Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.
```

## Computational vs. Relational Definitions

在某些情况下，Relational Definitions 比 Computational 更好。

例如加入了除法后，Relational Definitions 可以添加 evidence，而 Computational Definitions 则比较困难。

```coq
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).         (* <--- NEW *)

Reserved Notation "e '==>' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :          (* <----- NEW *)
      (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3
```

再比如加入一个 `AAny`，可能返回任何数字。由于 `AAny` 并不是将一个表达式转换为值，所以写起来就比较麻烦。

```coq
Inductive aexp : Type :=
  | AAny                           (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny ==> n                        (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)

where "a '==>' n" := (aevalR a n) : type_scope.
```

从中可以发现，如果定义比较难写成一个函数，或者无法写成一个函数时，应该用 Relation Definitions。如果二者都可以使用，那么 Relation Definitions 更容易理解，但是需要证明；而 Computational Definitions 更简洁，而且可以直接使用 Coq 内部机制进行求值，并且还可以生成 OCaml 或 Haskell 代码。在大型项目中二者都会提供，而且会证明二者等价。

# Expressions With Variables

## State

State 记录了当前程序中所有变量的值，可以用一个 `String -> Nat` 的 total map 实现，变量的值默认为 0。

```coq
Definition state := total_map nat.
```

## Syntax

```coq
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(* 定义变量 *)
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
```

## Notations

- `Coercion A: x >-> y`
  : 类型转换。Function/Constrcutor 可以用于 `x >-> y` 的**隐式类型转换**
- `Declare Custom Entry com`
  : 定义新语法，位于符号（如下文的 `<{}>`）之间的语句按照新的语法进行 Parse

```coq
(** Coercision for constructors **)
Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Definition example_aexp : aexp := <{ 3 + (X * 2) }>. (*[APlus 3 (AMult X 2)]*)
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>. (*[BAnd true (BNot (BLe X 4))]*)
```

用 `Set Printing Coercions.` 和 `Unset Printing Coercions.` 可以显示原始类型。

```coq
Print example_bexp.
(* ===> example_bexp = <{(true && ~ (X <= 4))}> *)

Set Printing Coercions.
Print example_bexp.
(* ===> example_bexp = <{(true && ~ (AId X <= ANum 4))}> *)

Unset Printing Coercions.
```

## Evaluation

对于变量的计算，只要将 state 传入即可

```coq
Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW，在 states map 里查找对应的值 *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.
```

建立 map，并测试两个函数。

```coq
Definition empty_st := (_ !-> 0). (* 对于不存在的变量默认为 `0` *)
Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

Example aexp1 :
    aeval (X !-> 5) <{ (3 + (X * 2))}>
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4)}>
  = true.
Proof. reflexivity. Qed.
```

# Commands (Statements)

## Syntax

BNF 定义如下：

```
c := skip | x := a | c ; c | if b then c else c end | while b do c end
```

```coq
Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
```

可以用一些 Notations 简化证明。

```coq
Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
```

一个例子：

```coq
Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while ~(Z = 0) do
       Y := Y * Z;
       Z := Z - 1
     end }>.
```

## Desugaring notations

可以通过 `Set Printing Coercions.` 或 `Unset Printing Notations.` 让 Coq 打印出不同的结果，防止在复杂的语法中迷失。

```coq
Print fact_in_coq. (* [Unset Printing Notations.] *)
(* ===>
   fact_in_coq =
   CSeq (CAss Z X)
        (CSeq (CAss Y (S O))
              (CWhile (BNot (BEq Z O))
                      (CSeq (CAss Y (AMult Y Z))
                            (CAss Z (AMinus Z (S O))))))
        : com *)

Print fact_in_coq. (* Set Printing Coercions. *)
(* ===>
  fact_in_coq =
  <{ Z := (AId X);
     Y := (ANum 1);
     while ~ (AId Z) = (ANum 0) do
       Y := (AId Y) * (AId Z);
       Z := (AId Z) - (ANum 1)
     end }>
       : com *)
```

## `locate` tactic

### Finding notations

对于未知的 Notations，可以用 `locate` 寻找含义。

```coq
Locate "&&".
(* ===>
    Notation
      "x && y" := BAnd x y (default interpretation)
      "x && y" := andb x y : bool_scope (default interpretation)
*)
```

### Finding identifiers

`locate` 也可以用来寻找定义。

```coq
Locate aexp.
(* ===>
     Inductive LF.Imp.aexp
     Inductive LF.Imp.AExp.aexp
       (shorter name to refer to it in current context is AExp.aexp)
     Inductive LF.Imp.aevalR_division.aexp
       (shorter name to refer to it in current context is aevalR_division.aexp)
     Inductive LF.Imp.aevalR_extended.aexp
       (shorter name to refer to it in current context is aevalR_extended.aexp)
*)
```

## Evalutaing Commands

在求值 Commands 的过程中，由于 `while` 循环是可以死循环的，所以求值过程会比较 tricky。

```coq
Definition loop : com :=
  <{ while true do
       skip
     end }>.
```

### Evaluation as function (FAIL)

用 function 去做 evaluation 的时候，Coq 由于不能判断这个函数会终止（实际上并不会终止）。

```coq
Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        (x !-> (aeval st a) ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | <{ while b do c end }> => (* WRONG *)
        if (beval st b)
          then ceval_fun st (s ; while b do c end)
          else st
  end.
```

Coq 报错 `("Error: Cannot guess decreasing argument of fix")`。

如果允许无穷递归，那么可以构造出值为 `False` 的命题。

```coq
Fixpoint loop_false (n : nat) : False := loop_false n.
(* [loop_false 0] will be a proof of False *)
```

### Evaluation as a Relation

将运算定义为 Relational 而非 Computational（即定义为 Prop 而非 Term）。

我们可以用记号 `st =[ c ]=> st'` 表示运算，读作 c takes state st to st'。

#### Operational Semantics

$$
\dfrac{}
{st =[ \operatorname{skip} ]\Rightarrow st}
\tag{E\_Skip}
$$

$$
\mathtt{
  \dfrac{\operatorname{aeval}\ st\ a = n}
  {st =[ x \coloneqq a ]\Rightarrow (x !\rightarrow n ; st)}
  \tag{E\_Ass}
}
$$

$$
\dfrac{st =[ \operatorname{c_1} ]\Rightarrow st',
       st' =[ \operatorname{c_2} ]\Rightarrow st''}
{st =[\operatorname{c_1; c_2}]\Rightarrow st''}
\tag{E\_Seq}
$$

$$
\dfrac{\operatorname{beval}\ st\ b = \operatorname{true},
       st =[ \operatorname{c_1}]\Rightarrow st'}
{st =[\operatorname{if}\ b\ \operatorname{then}\ \operatorname{c_1}
      \ \operatorname{else}\ \operatorname{c_2}\ \operatorname{end}]\Rightarrow st'}
\tag{E\_IfTrue}
$$

$$
\dfrac{\operatorname{beval}\ st\ b = \operatorname{false},
       st =[ \operatorname{c_2}]\Rightarrow st'}
{st =[\operatorname{if}\ b\ \operatorname{then}\ \operatorname{c_1}
      \ \operatorname{else}\ \operatorname{c_2}\ \operatorname{end}]\Rightarrow st'}
\tag{E\_IfFalse}
$$

$$
\dfrac{\operatorname{beval}\ st\ b = \operatorname{false}}
{st =[\operatorname{while}\ b\ \operatorname{do}\ \operatorname{c}\ \operatorname{end}]\Rightarrow st}
\tag{E\_WhileFalse}
$$

$$
\dfrac{\operatorname{beval}\ st\ b = \operatorname{true},
       st =[ \operatorname{c} ]\Rightarrow st',
       st'=[\operatorname{while}\ b\ \operatorname{do}\ \operatorname{c}\ \operatorname{end}]\Rightarrow st''}
{st =[\operatorname{while}\ b\ \operatorname{do}\ \operatorname{c}\ \operatorname{end}]\Rightarrow st''}
\tag{E\_WhileTrue}
$$

```coq
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').
```

用 Relation 代替 Function 的一个问题是不能自动求值了，必须要先算出值然后**证明**。

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
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    reflexivity.
    apply E_Ass. reflexivity.
Qed.
```

更复杂的一个例子：写一个求和 `Y = 1 + 2 + ... + X` 的程序，并证明其成立。

```coq
Definition pup_to_n : com :=
  <{Y := 0;
    while (1 <= X) do
          Y := Y + X;
        X := X - 1
    end }>.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  apply E_Seq with (Y !-> 0; X !-> 2).
  apply E_Ass. simpl. reflexivity.

  apply E_WhileTrue with (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2). simpl. reflexivity.
  apply E_Seq with (Y !-> 2; Y !-> 0; X !-> 2).
  apply E_Ass. simpl. reflexivity.
  apply E_Ass. simpl. reflexivity.

  apply E_WhileTrue with (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2). simpl. reflexivity.
  apply E_Seq with (Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
  apply E_Ass. simpl. reflexivity.
  apply E_Ass. simpl. reflexivity.

  apply E_WhileFalse. simpl. reflexivity. Qed.
```

### Determinism of Evaluation

Computational 形式下要求赋值一定是一个全函数，而 Relational 形式没有这个要求。

下面证明，求值是一个偏函数（partial function）。

```coq
Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.
```

# Reasoning About Imp Programs

关于程序的一些简单证明。

```coq
Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ X := X + 2 ]=> st' ->
  st' X = n + 2.
Proof.
Locate plus2.
  intros st n st' HX Heval.
  (* 用 [inversion] 可以展开程序 *)
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

Theorem loop_never_stops : forall st st',
  ~(st =[ while true do skip end ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
                                             eqn:Heqloopdef.
  try (induction contra; inversion Heqloopdef).
  - subst. inversion H.
  - subst. apply IHcontra2. reflexivity.
Qed.
```

## `no_whiles_terminating`

下面证明没有循环的程序一定会终止。

### 定义命题

首先用两种方式定义这个性质。

```coq
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }>  =>
      false
  end.

Inductive no_whilesR: com -> Prop :=
| E_NW_Skip : no_whilesR <{skip}>
| E_NW_Ass : forall x a1, no_whilesR <{x := a1}>
| E_NW_Seq : forall c1 c2, no_whilesR c1 ->
                      no_whilesR c2 ->
                      no_whilesR <{c1 ; c2}>
| E_NW_If : forall b ct cf, no_whilesR ct ->
                       no_whilesR cf ->
                       no_whilesR <{if b then ct else cf end}>.

```

证明二者等价（将问题转换为 relation）：

```coq
Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  { intros. induction c.
    - simpl; constructor.
    - constructor.
    - inversion H. apply andb_true_iff in H1. inversion H1.
      constructor. apply IHc1. assumption. apply IHc2. assumption.
    - inversion H. apply andb_true_iff in H1. inversion H1.
      constructor. apply IHc1. assumption. apply IHc2. assumption.
    - inversion H.
  }
  {
    intros. induction c.
    simpl; constructor.
    - constructor.
    - inversion H. simpl. apply IHc1 in H2. apply IHc2 in H3.
      rewrite H2. rewrite H3. reflexivity.
    - inversion H. simpl. apply IHc1 in H2. apply IHc2 in H4.
      rewrite H2. rewrite H4. reflexivity.
    - inversion H.
  }
Qed.
```

### 证明命题

需要注意的是不能先 `intros` 再 `induction`。在第三步的时候要证明 `exists st', st =[ c1; c2 ]=> st'`。

如果先 `intros` 会造成条件无用。

```coq
IHno_whilesR1 : exists st' : state, st =[ c1 ]=> st'
IHno_whilesR2 : exists st' : state, st =[ c2 ]=> st'
(* 我们要的是下面这种 *)
IHno_whilesR1' : forall st, exists st' : state, st =[ c1 ]=> st'
IHno_whilesR2' : forall st, exists st' : state, st =[ c2 ]=> st'
(* 这样就可以 [destruct] 出想要的条件 *)
IHno_whilesR1' : exists st' : state, st =[ c1 ]=> st'
IHno_whilesR2' : exists st'' : state, st' =[ c2 ]=> st''
(* -------------------------------- *)
exists st', st =[ c1; c2 ]=> st'
```

```coq
Theorem no_whiles_terminating : forall c st,
  no_whilesR c ->  exists st', st =[ c ]=> st'.
Proof.
  intros.
  generalize dependent st.
  induction H.
  - intros. exists st. apply E_Skip.
  - intros. exists (x !-> aeval st a1; st). apply E_Ass. reflexivity.
  - (* 重点 *)
    intros.
    destruct IHno_whilesR1 with st. destruct IHno_whilesR2 with x.
    exists x0. apply E_Seq with x. assumption. assumption.
  - intros.
    destruct IHno_whilesR1 with st. destruct IHno_whilesR2 with st.
    destruct (beval st b) eqn:Heqeb.
    + exists x. apply E_IfTrue. apply Heqeb. assumption.
    + exists x0.  apply E_IfFalse. apply Heqeb. assumption.
Qed.
```

# Additional Exerciese

## Stack Compiler

```
infix:   (2*3)+(3*(4-2))

postfix:  2 3 * 3 4 2 - * +
```

即将中缀表达式转为后缀表达式，并计算后缀表达式。

```coq
Inductive sinstr : Type :=
| SPush (n : nat)     (* Push the number [n] on the stack. *)
| SLoad (x : string)  (* Load the identifier [x] from the store and push it on the stack *)
| SPlus               (* Pop the two top numbers from the stack, add them, and push the result onto the stack. *)
| SMinus              (* Similar, but subtract the first number from the second. *)
| SMult.              (* Similar, but multiply. *)

(* 计算后缀表达式 *)

Fixpoint s_execute (st : state) (stack : list nat)
    (prog : list sinstr) : list nat :=
  match prog with
  | [] => stack
  | instr :: tl =>
    let nstack :=
      match instr with
      | SPush n => n :: stack
      | SLoad s => (st s) :: stack
      | SPlus => match stack with
        | n1 :: n2 :: stl => (n2 + n1) :: stl
        | _ => []
        end
      | SMinus => match stack with
        | n1 :: n2 :: stl => (n2 - n1) :: stl
        | _ => []
        end
      | SMult => match stack with
        | n1 :: n2 :: stl => (n2 * n1) :: stl
        | _ => []
        end
    end in s_execute st nstack tl
  end.

(* 中缀转后缀 *)
Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
  | AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.
```

要证明等价性，首先证明命题的加强形式，然后直接 `apply`。

```coq
Theorem execute_app : forall st p1 p2 stack,
    s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
    induction p1 as [|p1h p1t IH].
  - reflexivity.
  - destruct p1h; intros; try (apply IH).
Qed.

Lemma s_compile_correct_aux : forall e st stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  induction e; simpl; intros; subst; simpl;
    try (repeat (rewrite execute_app); rewrite IHe2; rewrite IHe1);
    reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. apply s_compile_correct_aux. Qed.
```

## 短路运算（short-circuit）

为 `And` 加入短路运算。

```coq
Fixpoint beval' (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => if (beval st b1) then (beval st b2) else false
  end.

Theorem beval_equalto_beval' : forall st b,
  beval st b = beval' st b.
Proof.
  intros.
  generalize dependent st.
  induction b; intros; simpl; reflexivity.
Qed.
```

## `break`

为语言加入 `break`。

首先重新定义一套 Notations。

```coq
Inductive com : Type :=
  | CSkip
  | CBreak                        (* <--- NEW *)
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'break'" := CBreak (in custom com at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
```

由于这两个语句都只对最近的循环起效，为了传递这种关系，要给 relation 加上一个 parameter 表示中断循环。

注意这里的 `SContinue` 不是“跳过本次循环执行下一次”，而是“不中断循环，和原来一样执行”。

```coq
Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).
```

下面讨论一下加上这个信号后的操作：
- 对于 `skip`，不改变 `state` 继续运行
- 对于 `break`，不改变 `state`，发出 `SBreak` 信号
- 对于 `:=`，更新 `state`，发出 `SContinue` 信号
- 对于 `if b then c1 else c2 end`，执行分支，并且从分支继承 `state` 和 `signal`
- 对于 `c1 ; c2`，执行 `c1`。如果收到了 `SBreak`，跳过 `c2` 并且传递 `SBreak`；否则继续执行 `c2`
- 对于循环 `while b do c end`，和原来一样执行，在判断条件时判断一下 `signal`，如果是 `SBreak` 则终止循环

```coq
Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  | E_Break : forall st,
      st =[ CBreak ]=> st / SBreak
  | E_Ass : forall a n x st,
      aeval st a = n ->
      st =[ CAss x a ]=> ( x !-> n ;st) / SContinue
  | E_Seq_Continue : forall c1 c2 st st' st'' sig,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / sig ->
      st =[ CSeq c1 c2 ]=> st'' / sig
  | E_Seq_Break : forall c1 c2 st st' ,
      st =[ c1 ]=> st' / SBreak ->
      st =[ CSeq c1 c2 ]=> st' / SBreak
  | E_If_True : forall b ct cf  st st' sig,
      beval st b = true ->
      st =[ ct ]=> st' / sig ->
      st =[ CIf b ct cf ]=> st' / sig
  | E_If_False : forall b ct cf st st' sig,
      beval st b = false ->
      st =[ cf ]=> st' / sig ->
      st =[ CIf b ct cf ]=> st' / sig
  | E_While_False : forall b c st,
      beval st b = false ->
      st =[ CWhile b c ]=> st / SContinue
  | E_While_True_Break : forall b c st st',
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ CWhile b c ]=> st' / SContinue
  | E_While_True_Continue : forall b c st st' st'',
      beval st b = true ->
      st =[ c ]=> st' / SContinue ->
      beval st'' b = false ->
      st' =[ CWhile b c ]=> st'' / SContinue ->
                           st =[ CWhile b c ]=> st'' / SContinue
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').
```

下面证明 `break` 行为的正确性。

```coq
Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof.
  intros. inversion H.
  - inversion H2.
  - inversion H5. reflexivity.
Qed.

Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
  intros.
  inversion H; reflexivity.
Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
  intros.
  inversion H0; constructor; subst; assumption.
Qed.

Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros.
  inversion H.
  - rewrite H0 in H4. inversion H4.
  - exists st. assumption.
  - rewrite H0 in H5. inversion H5.
Qed.
```

证明赋值是偏函数。

```coq
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  intros c st st1 st2 s1 s2 H1 H2.
  generalize dependent st2. generalize dependent s2.
  induction H1; (intros st2 s2 H2; inversion H2; subst; simpl).
  - auto.
  - auto.
  - auto.
  - apply IHceval2. apply IHceval1 in H1. inversion H1. rewrite H. assumption.
  - apply IHceval2. apply IHceval1 in H5. inversion H5. inversion H0.
  - apply IHceval in H3. inversion H3. inversion H0.
  - apply IHceval in H6. assumption.
  - apply IHceval. assumption.
  - rewrite H8 in H. inversion H.
  - rewrite H8 in H. inversion H.
  - apply IHceval. assumption.
  - auto.
  - rewrite H3 in H. inversion H.
  - rewrite H3 in H. inversion H.
  - rewrite H7 in H. inversion H.
  - apply IHceval in H8. inversion H8. rewrite H0. auto.
  - apply IHceval in H5. inversion H5. inversion H3.
  - rewrite H in H7. inversion H7.
  - apply IHceval1 in H8. inversion H8. inversion H3.
  - apply IHceval1 in H5. inversion H5. rewrite <- H1 in H10. apply IHceval2 in H10. assumption.
Qed.
```
