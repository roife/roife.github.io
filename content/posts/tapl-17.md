+++
title = "[TaPL] 17 Subtyping in ML"
author = ["roife"]
date = 2024-07-22
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论", "程序语义", "subtyping"]
draft = false
+++

Subtyping 的实现基于 STLC。由于前面给出了 algorithmic subtyping 的实现，因此这里直接对着写就行。


## Syntax {#syntax}

```ocaml
type ty =
    TyRecord of (string * ty) list           (** new **)
  | TyTop                                    (** new **)
  | TyArr of ty * ty

type term =
    TmRecord of info * (string * term) list  (** new **)
  | TmProj of info * term * string           (** new **)
  | TmVar of info * int * int
  | TmAbs of info * string * ty * term
  | TmApp of info * term * term
```


## Subtyping {#subtyping}

```ocaml
let rec subtype tyS tyT =
  (=) tyS tyT ||
  match (tyS, tyT) with
  | (TyRecord(fS), TyRecord(fT)) ->
      List.for_all (fun (li, tyTi) ->
          try
            let tySi = List.assoc li fS in
            subtype tySi tyTi
          with Not_found -> false) fT
  | (_, TyTop) ->
      true
  | (TyArr(tyS1, tyS2), TyArr(tyT1, tyT2)) ->
      (subtype tyT1 tyS1) && (subtype tyS2 tyT2)
  | (_, _) ->
      false
```

这里比较特殊的地方是在头部加了一个 \`(=) tyS tyT\`，这是因为在现实场景中，大多数情况下两个类型都是相等的，因此可以通过这个短路来提高性能。


## Typing {#typing}

```ocaml
let rec typeof ctx t =
  match t with
  | TmRecord(fi, fields) ->
      let fieldtys = List.map (fun (li, ti) -> (li, typeof ctx ti)) fields in
      TyRecord(fieldtys)
  | TmProj(fi, t1, l) ->
      (match (typeof ctx t1) with
        | TyRecord(fieldtys) ->
            (try
              List.assoc l fieldtys
            with Not_found -> error fi ("label " ^ l ^ " not found"))
        | _ -> error fi "Expected record type")
  | TmVar(fi, i, _) ->
      getTypeFromContext fi ctx i
  | TmAbs(fi, x, tyT1, t2) ->
      let ctx' = addbinding ctx x (VarBind(tyT1)) in
      let tyT2 = typeof ctx' t2 in
      TyArr(tyT1, tyT2)
  | TmApp(fi, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match tyT1 with
        | TyArr(tyT11, tyT12) ->
            if subtype tyT2 tyT11 then tyT12
            else error fi "parameter type mismatch"
        | _ -> error fi "arrow type expected")
```

这里主要新增了对于 record 类型的处理，以及在 application 中加入了 subtype 的检查。


## Joins and meets {#joins-and-meets}

```ocaml
let rec join tyS tyT =
  match (tyS, tyT) with
  | (TyArr(tyS1, tyS2), TyArr(tyT1, tyT2)) ->
      (try TyArr(meet tyS1 tyT1, join tyS2 tyT2)
       with Not_found -> TyTop)
  | (TyBool, TyBool) ->
      TyBool
  | (TyRecord(fS), TyRecord(fT)) ->
      let labelsS = List.map (fun (li, _) -> li) fS in
      let labelsT = List.map (fun (li, _) -> li) fT in
      let commonLabels =
        List.find_all (fun l -> List.mem l labelsT) labelsS in
      let commonFields =
        List.map (fun li ->
            let tySi = List.assoc li fS in
            let tyTi = List.assoc li fT in
            (li, join tySi tyTi))
          commonLabels in
      TyRecord(commonFields)
  | _ -> TyTop

and meet tyS tyT =
  match (tyS, tyT) with
  | (TyArr(tyS1, tyS2), TyArr(tyT1, tyT2)) ->
      TyArr(join tyS1 tyT1, meet tyS2 tyT2)
  | (TyBool, TyBool) ->
      TyBool
  | (TyRecord(fS), TyRecord(fT)) ->
      let labelsS = List.map (fun (li, _) -> li) fS in
      let labelsT = List.map (fun (li, _) -> li) fT in
      let allLabels =
        List.append
          labelsS
          (List.find_all (fun l -> not (List.mem l labelsS)) labelsT) in
      let allFields = List.map (fun li ->
          if List.mem li allLabels then
            let tySi = List.assoc li fS in
            let tyTi = List.assoc li fT in
            (li, meet tySi tyTi)
          else if List.mem li labelsS then
            (li, List.assoc li fS)
          else
            (li, List.assoc li fT))
        allLabels in
      TyRecord(allFields)
  | _ -> raise Not_found

let rec typeof ctx t =
  match t with
  | TmTrue(fi) ->
      TyBool
  | TmFalse(fi) ->
      TyBool
  | TmIf(fi, t1, t2, t3) ->
      if subtype (typeof ctx t1) TyBool then
        join (typeof ctx t2) (typeof ctx t3)
      else
        error fi "guard of conditional not a boolean"
```


## Bot {#bot}

```ocaml
type ty =
    TyRecord of (string * ty) list
  | TyTop
  | TyBot                                    (** new **)
  | TyArr of ty * ty

let rec subtype tyS tyT =
  (=) tyS tyT ||
  match (tyS, tyT) with
  | (TyRecord(fS), TyRecord(fT)) ->
      List.for_all (fun (li, tyTi) ->
          try
            let tySi = List.assoc li fS in
            subtype tySi tyTi
          with Not_found -> false) fT
  | (_, TyTop) ->
      true
  | (TyBot, _) ->                            (** new **)
      true
  | (TyArr(tyS1, tyS2), TyArr(tyT1, tyT2)) ->
      (subtype tyT1 tyS1) && (subtype tyS2 tyT2)
  | (_, _) ->
      false

let rec typeof ctx t =
  match t with
  | TmRecord(fi, fields) ->
      let fieldtys = List.map (fun (li, ti) -> (li, typeof ctx ti)) fields in
      TyRecord(fieldtys)
  | TmProj(fi, t1, l) ->
      (match (typeof ctx t1) with
        | TyRecord(fieldtys) ->
            (try
              List.assoc l fieldtys
            with Not_found -> error fi ("label " ^ l ^ " not found"))
        | TyBot -> TyBot
        | _ -> error fi "Expected record type")
  | TmVar(fi, i, _) ->
      getTypeFromContext fi ctx i
  | TmAbs(fi, x, tyT1, t2) ->
      let ctx' = addbinding ctx x (VarBind(tyT1)) in
      let tyT2 = typeof ctx' t2 in
      TyArr(tyT1, tyT2)
  | TmApp(fi, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match tyT1 with
        | TyArr(tyT11, tyT12) ->
            if subtype tyT2 tyT11 then tyT12
            else error fi "parameter type mismatch"
        | TyBot -> TyBot
        | _ -> error fi "arrow type expected")
```
