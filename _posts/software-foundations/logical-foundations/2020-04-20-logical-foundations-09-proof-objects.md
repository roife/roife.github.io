---
layout: "post"
title: "「SF-LF」 09 Proof Objects"
subtitle: "The Curry-Howard Correspondence"
author: "roife"
date: 2020-04-20

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论", "C-H 同构@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Curry-Howard Correspondence

> Algorithms are the computational content of proofs. –Robert Harper

Coq 的语法中既有用于 Programming 的部分（如 inductive 类型），又有 Proving 的部分（如 inductive 命题），二者相似。暗示了在 Coq 中 Programming 和 Proving 本质上或许有联系。

logic 和 computation 之间有一种对应关系，即 Curry-Howard Correspondence。在 Coq 中构建命题的证明实际上是在构建一棵 evidence 树，这样的树可以看作一种 evidence 的数据结构，此时命题则可以被看作它的类型。用已有命题去证明新命题的过程，可以看作用已有类型构建新类型。

``` example
propositions ~ types
proofs/evidence ~ data values
```

如 `ev_0 : even 0` 可以有两种方式解读：

- 从 Programming 的角度看，`ev_0` 的类型为 `even 0`，此时程序为类型间的转换
- 从 Proving 的角度看，`ev_0` 是 `even 0` 的 evidence，此时程序为对命题的证明

# Proof Objects & Proof Scripts

命题构建完成的结果为一个 Proof Obejects。`Proof.` 和 `Qed.` 之间的部分（即 tactics）对应着命题逐步构造的过程，等价于直接给出 evidence 树（即直接用 `Definition` 给出 Proof Objects 和 `Theorem` 中用 tactics 构建）。可以看出 `Definition` 和 `Theorem` 之间存在对应关系。

``` coq
Theorem ev_4 : even 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

(* 查看命题生成的 Proof Objects *)
Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)
             : even 4  *)

(* 不用 tactics 直接给出 Proof Objects *)
Definition ev_4''' : even 4 :=
  ev_SS 2 (ev_SS 0 ev_0).
```

- `Show Proof`：输出目前部分完成的命题，`?Goal` 为暂未完成的部分，称为“hole”，对应着一个 subgoal

``` coq
Theorem ev_4'' : even 4.   (*  match? (even 4) *)
Proof.
  Show Proof.              (*  ?Goal  *)
  apply ev_SS.
  Show Proof.              (*  (ev_SS 2 ?Goal)  *)
  apply ev_SS.
  Show Proof.              (*  (ev_SS 2 (ev_SS 0 ?Goal))  *)
  apply ev_0.
  Show Proof.              (*  ?Goal (ev_SS 2 (ev_SS 0 ev_0))  *)
Qed.
```

# Quantifiers, Implications, Functions

在 Computational 的部分中，箭头（`=>`）用处有两个

- `Inductive` 定义数据类型中的 constructor
- 定义函数

在 logical 的部分中，箭头（`->`）也有两个用处

- `Inductive` 定义的 propositions
- 定义函数（即之前提到的命题可以被当成函数使用）

``` coq
Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n H. apply ev_SS. apply ev_SS. apply H.
Qed.

Definition ev_plus4' : forall n, even n -> even (4 + n) :=
  fun (n : nat) ⇒ fun (H : even n) =>
    ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : even n)
                    : even (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).
```

其中 `even n` 的类型依赖于第一个变量 `n`，这就是 dependent type。

可以发现 `forall` 和 `->` 都和函数对应，实际上 `->` 是特殊的 `forall`，区别在于 `->` 不需要给参数具体名称。`P -> Q` 等价于 `forall (_:P), Q`。

``` coq
(* [forall n, forall(E : even n), even (n + 2).]
[= forall n, forall(_ : even n), even (n + 2).]
[= forall n, even n -> even (n + 2).] *)
```

# Programming with tactics

Proving 可以用 Programming 的写法来写（直接给出 Proof Objects），同样 Programming 也可以用 Proving 的方式写（使用 tactics）。

``` coq
Definition add1 : nat -> nat.
intro n. apply S. apply n. Defined.
```

其中 `:=` 变成了 `.`，暗示要用 Proof scripts，结尾也变成了 `Defined.` 而非 `Qed.`。（用 `Qed.` 就无法在函数中使用了）

这种写法常用来写 dependent type functions。

# Logical connectives

除了全称量词用函数表达，其它的逻辑连接词都可以用 inductive 表达。

## Conjunction

``` coq
Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q. (*[conj (A:P) (B:Q) : and P Q]*)

Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)
```

可以发现 `and` 类似于 product type，这就是 `destruct` 和 `intros` 能用在 conjunction 上的原因（本质上是对 `inductive` 操作）。反过来，`split` 也可以用在只有一个 constructor 的 `inductive` 类型上（`<->` 本质上是 `and`）。

``` coq
(* 从 proving 和 programming 两个角度分别构建 Proof objects *)
Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
- intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
- intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P := (* [(P : Prop) -> (Q : Prop) -> (P /\ Q) -> (Q /\ P)] *)
  match H with
  | conj HP HQ => conj HQ HP (* 此处注意 conj 只接受了两个参数 A B, 缺失了两个参数 P Q, 原因见下 *)
  end.
```

## Disjunction

``` coq
Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q (*[or_introl (A : P) : or P Q]*)
| or_intror : Q -> or P Q.
```

从这个定义不难看出为什么 `destruct` 可以对 `or` 生效（等价于对 `Inductive` 进行 `destruct`）。

## Existential Quantification

``` coq
Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P. (* [ex_intro {A : Type} (P : A -> P) (x : A) (H : P x) : ex P.] *)
```

`ex_intro` 只要需要三个参数，依次是命题 `P`，witness `x`，结论 `P x`。

`exists` tactic 相当于 `apply ex_intro`。

``` coq
Definition some_nat_is_even : ∃n, even n :=
  ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).

Definition ex_ev_Sn : ex (fun n => even (S n)) :=
  ex_intro (fun n => even (S n)) 1 (ev_SS 0 ev_0).
```

## Sugars in builtin Definitions

### conj

``` coq
Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun P Q R (H1: and P Q) (H2: and Q R) =>
    match (H1,H2) with
    (* [| (conj HP HQ, conj HQ2 HR) => conj HP HR ]*)
    | (@conj _ _ HP _, @conj _ _ _ HR) => @conj P R HP HR
    end.

Print and.
(* ==> *)
Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B

For conj: Arguments A, B are implicit
For and: Argument scopes are [type_scope type_scope]
For conj: Argument scopes are [type_scope type_scope _ _]
```

可以看到，Coq 内置的 `and` 类型中，`A, B` 为 implicit arguments。

### or_introl and or_intror

``` coq
Definition or_comm : forall (P:Prop) (Q:Prop), P \/ Q -> or Q \/ P :=
  fun P Q H ⇒
      match H with
      (* [| or_introl P => or_intror P]
         [| or_intror Q => or_introl Q]*)
      | or_introl HP => @or_intror Q P HP
      | or_intror HQ => @or_introl Q P HQ
      end.

Print or.
(* ==> *)
Inductive or (A B : Prop) : Prop :=  or_introl : A -> A \/ B | or_intror : B -> A \/ B

For or_introl, when applied to no more than 1 argument:
  Arguments A, B are implicit
For or_introl, when applied to 2 arguments:
  Argument A is implicit
For or_intror, when applied to no more than 1 argument:
  Arguments A, B are implicit
For or_intror, when applied to 2 arguments:
  Argument B is implicit
For or: Argument scopes are [type_scope type_scope]
For or_introl: Argument scopes are [type_scope type_scope _]
For or_intror: Argument scopes are [type_scope type_scope _]
```

`or_introl` 和 `or_intror` 不仅使用了 implicit arguments, 还发生了重载。

### ex_intro

``` coq
Print ex.
(* Coq 内部 ==> *)
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> exists y, P y

For ex: Argument A is implicit
For ex_intro: Argument A is implicit
For ex: Argument scopes are [type_scope function_scope]
For ex_intro: Argument scopes are [type_scope function_scope _ _]

(* 自定义 ==>*)
Inductive ex (A : Type) (P : A -> Prop) : Prop :=  ex_intro : forall x : A, P x -> ex P

For ex: Argument A is implicit and maximally inserted
For ex_intro: Argument A is implicit and maximally inserted
For ex: Argument scopes are [type_scope function_scope]
For ex_intro: Argument scopes are [type_scope function_scope _ _]
```

可以看到 Coq 内部的和自定义的略微有区别。

这就是为什么普通使用时可以不传入类型。

# True and False

``` coq
Inductive True : Prop :=
  | I : True.

Inductive False : Prop := .
```

- `True` 只有一个 constructor，因此对于所有 `True` 的证明都是等价的
- `False` 没有 constructor，因此不可能构造出一个 `False` 的 evidence

# Equality

``` coq
Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.
```

对于给定的类型，`eq` 定义了一系列命题。

对于普通的类型，Coq 会自动化简。

``` coq
Lemma four: 2 + 2 == 1 + 3.
Proof. apply eq_refl. Qed.

Definition four' : 2 + 2 == 1 + 3 := eq_refl 4.
```

# Inversion, Again

`inversion`

- 传入一个 hypotheses `H` 并且要求其中的类型 `P` 是归纳定义的
- 对于类型 `P` 中的每一个 constructor `C` 做以下的事：
  - 生成一个 subgoal, 并假设 `C` 导出了 `H`
  - 将 `C` 的参数和假设添加到当前的条件（上下文） 中
  - 将 conclusion 和与当前的 goal 相匹配，并为 `C` 的成立添加一些等式到条件中（并自动执行一些 tactics）
  - 如果这些等式不成立，那么忽略这种情况
