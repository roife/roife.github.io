+++
title = "[TaPL] 07 Lambda-Calculus in ML"
author = ["roife"]
date = 2021-04-25
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论", "程序语义", "Lambda演算", "de Bruijn"]
draft = false
+++

## Terms and Contexts {#terms-and-contexts}

基于 de Bruijn indices 定义 Lambda 表达式的语法：

```ocaml
type term =
    TmVar of int
  | TmAbs of term
  | TmApp of term * term
```

为了方便调试，还可以增加三个优化：

1.  `info` 用来保存 parse 的信息（例如行号等），方便错误提示
2.  对于变量，可以增加一个 `int` 表示 context 的总长度，用来检验 shift 是否正确
3.  对于 term，增加一个字符串信息用来打印，将 de Bruijn terms 转换回原来的 term

<!--listend-->

```ocaml
type term =
    TmVar of info * int * int
  | TmAbs of info * string * term
  | TmApp of info * term * term
```

下面是用于打印的方法。

```ocaml
type binding = NameBind
type context = (string * binding) list

let rec printtm ctx t = match t with
    TmAbs(fi, x, t1) ->
      let (ctx', x') = pickfreshname ctx x in
      pr "(lambda "; pr x'; pr ". "; printtm ctx' t1; pr ")"
  | TmApp(fi, t1, t2) ->
      pr "("; printtm ctx t1; pt " "; printtm ctx t2; pr ")"
  | TmVar(fi, x, n) ->
      if ctxlength ctx = n them
        pr (index2name fi ctx x)
      else
        pr "[bad index]"
```

此处的 `context` 用 `list` 记录了当前的上下文，其中的 `binding` 在此处没有特别的作用，可以省略。

`pr` 用于打印字符到标准输出，`ctxlength` 用于返回 context 的长度，`index2name` 会根据 index 返回字符串，`pickfreshname` 通过 `ctx` 和 hint string `x` 查找一个不在 `ctx` 中的 `x'`，并返回 `ctx'` 与 `x'`。

在实际的程序中会用更复杂的 print 策略，例如添加括号、换行等。

在实现时，`context` 遵循 naming context 的规则，即 de Bruijn indices \\(i \mapsto \operatorname{\mathtt{context}}\_{\operatorname{\mathtt{len}} - i - 1}\\)。创建内部的 abstraction 时，直接在 `context` 尾部压入新的名字即可。


## Shifting and Substitution {#shifting-and-substitution}

Shift 操作 \\(\uparrow^d (t)\\) 的实现和数学定义差不多：

```ocaml
let termShift d t =
  let rec walk c t = match t with
    TmVar(fi, x, n) -> if x >= c then TmVar(fi, x+d, n+d)
              else TmVar(fi, x, n+d)
  | TmAbs(fi, x, t1) -> TmAbs(fi, x, walk (c+1) t1)
  | TmApp(fi, t1, t2) -> TmApp(fi, walk c t1, walk c t2)
  in walk 0 t
```

这里用一个内部函数 `walk` 来实现递归。由于 \\(d\\) 是始终不变的，所以可以作为外部变量。

下面是 substitution \\([j \mapsto s]t\\) 的实现：

```ocaml
let termSubst j s t =
  let rec walk c t = match t with
    TmVar(fi, x, n) -> if x == j+c then termShift c s
                        else TmVar(fi, x, n)
  | TmAbs(fi, x, t1) -> TmAbs(fi, x, walk (c+1) t1)
  | TmApp(fi, t1, t2) -> TmApp(fi, walk c t1, walk c t2)
  in walk 0 t
```

此处为了统一，记录一个额外的 \\(c\\) 表示当前所在的层级，因此公式中的 \\(j\\) 在代码中为 \\(j + c\\)。此时可以发现 `termShift` 和 `termSubst` 的定义非常相似，唯一的区别在于归纳的叶子节点 `TmVar`。基于这一点，可以写出一个统一二者的函数 `tmmap`。

```ocaml
let tmmap onvar c t =
  let rec walk c t = match t with
    TmVar(fi,x,n) -> onvar fi c x n
  | TmAbs(fi,x,t2) -> TmAbs(fi,x,walk (c+1) t2)
  | TmApp(fi,t1,t2) -> TmApp(fi,walk c t1,walk c t2)
  in walk c t

let termShiftAbove d c t =
  tmmap
    (fun fi c x n -> if x>=c then TmVar(fi,x+d,n+d) else TmVar(fi,x,n+d))
    c t

let termShift d t = termShiftAbove d 0 t
```

在 beta-conversion 中，一共包含了三个步骤：

1.  shift the term being substituted
2.  substitution
3.  shift down the whole result

<!--listend-->

```ocaml
let termSubstTop s t =
  termShift (-1) (termSubst 0 (termShift 1 s) t)
```


## Evaluation {#evaluation}

```ocaml
let rec isval ctx t = match t with
    TmAbs(_, _, _) -> true
  | _ -> false

exception NoRuleApplies

let rec eval1 ctx t = match t with
    TmApp(fi, TmAbs(_, x, t12), v2) when isval ctx v2 ->
      termSubstTop v2 t12
  | TmApp(fi, v1, t2) when isval ctx v1 ->
      let t2' = eval1 ctx t2 in
      TmApp(fi, v1, t2')
  | TmApp(fi, t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmApp(fi, t1', t2)
  | _ ->
      raise NoRuleApplies

let rec eval ctx t =
  try let t' = eval1 ctx t
      in eval ctx t'
  with NoRuleApplies -> t
```

相比 Chapter 3，这里多了一个将来会用到的 `ctx`。
