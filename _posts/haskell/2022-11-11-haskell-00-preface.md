---
layout: "post"
title: "「Haskell 学习」 00 Introduction"
subtitle: "Haskell 简介"
author: "roife"
date: 2022-11-11

tags: ["Haskell@编程语言", "函数式编程@Tags", "Haskell 函数式入门@读书笔记", "读书笔记@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

> 本教程主要参考《Haskell 函数式编程入门》

# 介绍

在 Haskell 出现之前，就已经诞生了很多基于函数式思想的语言，例如 1958 年 John McCarthy 设计的 Lisp、1975 年的 Scheme 以及同时期的 ML 等。在 1987 年的 FPCA'87 上，为了能够解决现有的函数式语言种类过多的问题，决定制定了一个开放式的语言来整合现有的函数式语言，即 Haskell。

Haskell 在 1985 年发行的 Miranda 基础上进行标准化，并以 λ 演算为基础发展而来。在现有的 Haskell 编译器中，用的最广泛的是 GHC（Glasgow Haskell Compiler）。

## GHCi

GHCi 是一个 Haskell 的交互式解释器，这里记录一些常用的命令：
- 导入文件
  - `:load`（`:l`）：从当前路径导入文件
  - `:reload`（`:r`）：重新导入代码文件
  - `:cd`：进入目录
  - `:edit`：用默认的 editor（`$EDITOR`）编辑导入的文件
- `module`（`:m +<module>`/`:m -<module>`）：导入模块、移除模块
- 查看
  - `:type`（`:t`）：查看类型
  - `:kind`（`:k`）：查看 `kind`
  - `:i`：查看类型、函数或 typeclasses 的信息
- `:set -X`：开启语言扩展
- `:!`：执行命令行（`:! clear` 很好用）

在 GHCi 中不能写多行定义，需要用 `:{ :}` 进行包裹：

```haskell
:{
  foo :: Int -> Int;
  foo 1 = 2
  foo n = 0
:}
```

## 文件后缀与注释

Haskell 代码一般用 `.hs` 作为后缀，也可以用 `.lhs` 进行文学编程。

注释一般用 `--`（单行）和 `{--}`（多行）。在文件首部的 `{-##-}` 一般用于开启编译选项。
