+++
title = "[TaPL] 10 STLC in ML"
author = ["roife"]
date = 2021-05-05
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论", "程序语义", "STLC"]
draft = false
+++

\\(\lambda\_\rightarrow\\) 的实现和 untyped λ 演算类似，主要是添加了一个 `typeof` 函数用于计算类型。


## Contexts {#contexts}

在 untyped λ 演算中使用了 `context` 记录上下文，当时使用的 `binding` 只有一个空的 constructor `NameBind`。此处为了记录类型，使用了一个新的 constructor `VarBind` 来携带类型。原来的 `NameBind` 仍然保留，用于解析和打印（此时不关心类型）。

```ocaml
type binding =
    NameBind
  | VarBind of ty
```

此外，有几个辅助的函数用于操作 contexts：

```ocaml
let addbinding ctx x bind = (x,bind)::ctx

let rec getbinding fi ctx i =
  try
    let (_, bind) = List.nth ctx i in
    bind
  with Failure _ ->
    error fi ("Variable lookup failure: offset")

let getTypeFromContext fi ctx i =
  match getbinding fi ctx i with
      VarBind(tyT) → tyT
    |_ -> error fi
      ("getTypeFromContext: Wrong kind of binding for variable "
       ^ (index2name fi ctx i))
```


## Terms and Types {#terms-and-types}

类型的数据类型定义如下：

```ocaml
type ty =
    TyBool
  | TyArr of ty * ty
```

term 的定义如下，唯一值得注意的是在 `TmAbs` 中增加了类型的数据：

```ocaml
type term =
    TmTrue of info
  | TmFalse of info
  | TmIf of info * term * term * term
  | TmVar of info * int * int
  | TmAbs of info * string * ty * term
  | TmApp of info * term * term
```


## Typechecking {#typechecking}

`typeof` 可以看成是 \\(\lambda\_\rightarrow\\) 的 typing rules 的翻译，也可以看成是 inversion lemma 的翻译。前者说明了在某些条件下 term 是 well-typed 的，而后者说明了 well-typeness 需要满足的条件，因此后者更加准确。

```ocaml
let rec typeof ctx t =
  match t with
      TmTrue(fi) -> TyBool
    | TmFalse(fi) -> TyBool
    | TmIf(fi, t1, t2, t3) ->
       if (=) (typeof ctx t1) TyBool then
         let tyT2 = typeof ctx t2 in
           if (=) tyT2 (typeof ctx t3) then tyT2
           else error fi "arms of conditional have different types"
       else error fi "guard of conditional not a boolean"
    | TmVar(fi, i, _) -> getTypeFromContext fi ctx i
    | TmAbs(fi, x, tyT1, t2) ->
       let ctx’ = addbinding ctx x (VarBind(tyT1)) in
       let tyT2 = typeof ctx’ t2 in
       TyArr(tyT1, tyT2)
    | TmApp(fi,t1,t2) →
         let tyT1 = typeof ctx t1 in
           let tyT2 = typeof ctx t2 in
             (match tyT1 with
               TyArr(tyT11, tyT12) →
                 if (=) tyT2 tyT11 then tyT12
                 else error fi "parameter type mismatch"
               | _ → error fi "arrow type expected")
```
