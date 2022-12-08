---
layout: "post"
title: "「TaPL」 04 Arithmetic Expressions in ML"
subtitle: "用 ML 实现算术表达式"
author: "roife"
date: 2021-04-13

tags: ["Types and Programming Languages@读书笔记", "读书笔记@Tags", "类型系统@程序语言理论", "程序语言理论@Tags", "OCaml@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# Syntax

```ocaml
type term =
  TmTrue of info
| TmFalse of info
| TmIf of info * term * term * term
| TmZero of info
| TmSucc of info * term
| TmPred of info * term
| TmIsZero of info * term
```

`info` 用来保存 parse 的信息，可以被省略。

- 检验一个 `term` 是否是数字：

    ```ocaml
    let rec isnumericval t = match t with
      TmZero(_) -> true
    | TmSucc(_, t1) -> isnumericval t1
    | _ -> false
    ```

- 检验 `term` 的合法性：

    ```ocaml
    let rec isval t = match t with
      TmTrue(_) -> true
    | TmFalse(_) -> true
    | t when isnumericval t -> true
    | _ -> false
    ```

# Evaluation

首先定义一个辅助函数，它是一个 partial function。如果传入的 `term` 可以被化简，则它返回化简一步得到的结果，直到不能被化简时产生一个异常。

```ocaml
exception NoRuleApplies

let rec eval1 t = match t with
  TmIf(_,TmTrue(_),t2,t3) ->
    t2
| TmIf(_,TmFalse(_),t2,t3) ->
    t3
| TmIf(fi,t1,t2,t3) ->
    let t1' = eval1 t1 in
    TmIf(fi, t1', t2, t3)
| TmSucc(fi,t1) ->
    let t1' = eval1 t1 in
    TmSucc(fi, t1')
| TmPred(_,TmZero(_)) ->
    TmZero(dummyinfo)
| TmPred(_,TmSucc(_,nv1)) when (isnumericval nv1) ->
    nv1
| TmPred(fi,t1) ->
    let t1' = eval1 t1 in
    TmPred(fi, t1')
| TmIsZero(_,TmZero(_)) ->
    TmTrue(dummyinfo)
| TmIsZero(_,TmSucc(_,nv1)) when (isnumericval nv1) ->
    TmFalse(dummyinfo)
| TmIsZero(fi,t1) ->
    let t1' = eval1 t1 in
    TmIsZero(fi, t1')
| _->
    raise NoRuleApplies
```

这里还添加了一些额外的数据（比如返回的 `TmTrue(dummyinfo)`）。由于这些数据是程序生成的，而不是 parse 得到的，所以它们的 `info` 是 `dummyinfo`。

`fi` 表示 `file information`，用来匹配 `info`。

```ocaml
let rec eval t =
  try let t' = eval1 t
      in eval t'
  with NoRuleApplies -> t
```

## Big-step Evaluation

```ocaml
exception NoRuleApplies

let rec eval2 t = match t with
  TmTrue(_) -> t
| TmFalse(_) -> t
| TmZero(_) -> t
| TmIf(_,t1,t2,t3) ->
    match eval2 t1 with
      TmTrue(_) -> eval2 t2
    | TmFalse(_) -> eval2 t3
    | _ -> raise NoRuleApplies
| TmSucc(fi,t1) ->
  (match eval2 t1 with
   nv when (isnumericval nv) -> TmSucc(fi,nv)
   | _ -> raise NoRuleApplies)
| TmPred(fi,t1) ->
  (match eval2 t1 with
   TmZero(_) -> TmZero(dummyinfo)
   | TmSucc(_,nv) when (isnumericval nv) -> TmPred(fi,nv)
   | _ -> raise NoRuleApplies)
| TmIsZero(fi,t1) ->
  (match eval2 t1 with
   TmZero(_) -> TmTrue(dummyinfo)
   | nv when (isnumericval nv) -> TmFalse(dummyinfo)
   | _ -> raise NoRuleApplies)

let rec eval3 t =
  try eval2 t
  with NoRuleApplies → t
```