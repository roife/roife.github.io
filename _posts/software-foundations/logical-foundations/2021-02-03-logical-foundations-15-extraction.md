---
layout: "post"
title: "「SF-LF」 15 Extraction"
subtitle: "Extraction ML from Coq"
author: "roife"
date: 2021-02-03

tags: ["Software Foundations@读书笔记", "SF | Logical Foundations@读书笔记", "读书笔记@Tags", "程序语言理论@Tags", "Coq@编程语言", "形式化验证@程序语言理论"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# Basic Extraction

- OCaml : most mature
- Haskell : mostly works
- Scheme : a bit out of date

```coq
Extraction "imp1.ml" ceval_step.
(* 运行结果：会一同将 dependencies 导出
The file imp1.ml has been created by extraction.
The file imp1.mli has been created by extraction.
*)
```

# Controlling Extraction of Specific Types

Coq 可以指明导出的 `Inductive` 类型和其 constructor 对应 OCaml 中的什么类型。

```coq
Extract Inductive bool => "bool" [ "true" "false" ].
```

对于 non-enumeration（即 constructor 接受参数），也可以制定一个作为 recursor 的表达式（比如 Church Numbers）：

```coq
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

(* 也可以对应到terms 或 operators *)
Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".
```

对应的正确性要靠导出者保证，例如下面这个表达式。在 Coq 中 `0 - 1 = 0`，但是在 OCaml 中 `0 - 1 = -1`。

```coq
Extract Constant minus ⇒ "( - )".
```

# A Complete Example

导出 Imp Interpreter。

```coq
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extract Inductive sumbool => "bool" ["true" "false"].

From LF Require Import Imp.
From LF Require Import ImpParser.

From LF Require Import Maps.
Extraction "imp.ml" empty_st ceval_step parse.
```

然后就可以编译运行了。

```shell
$ ocamlc -w -20 -w -26 -o impdriver imp.mli imp.ml impdriver.ml
$ ./impdriver
```

由于之前证明了其正确性，所以这是一个 **certified** Imp interpreter。
