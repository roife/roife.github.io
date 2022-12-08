---
layout: "post"
title: "「PKU - Software Analysis」 03 SSA and Sparse Analysis"
subtitle: "SSA 与稀疏分析"
author: "roife"
date: 2021-10-07

tags: ["程序分析@Tags", "北大软件分析@课程相关", "课程相关@Tags", "SSA@编译", "编译@Tags", "IR@编译"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# Def-Use 关系

给定变量 x，如果结点 A 可能改变 x 的值，结点 B 可能使用结点 A 的新值，则结点 A 和结点 B 存在 Def-Use 关系。

传统的数据流分析每个结点都需要保存所有变量的信息，但是实际上每个变量只有在 Def-Use 处被改变，所以可以只沿着 Def-Use 边传递抽象值，每个结点只保存自己定义的变量的抽
象值。此时图变得稀疏，这样可以加快数据流分析。

但是单纯的 Def-Use 关系有两个问题：
- 维护 Def-Use 关系：用 Reaching Definition 太慢了
- 分支中的 Def-Use 太多，那么会产生更多的边

可以用 SSA 减少依赖的边，加速分析。

# SSA

SSA 中每个变量都只被赋值一次。并引入了 $\varphi$ 函数处理分支的情况。

$$
y \gets \varphi(x_1 : B_1, x_2 : B_2, \dots, x_n : B_n)
$$

从基本块 $B_i$ 过来时，取 $y_i \gets x_i$。

## 好处

- 静态单赋值直接提供了 Def-Use 链（因为只赋值了一次，唯一定义 `x` 的地方是 def，所有用了 `x` 的地方都是 use）
- 静态单赋值存在高效算法
- 静态单赋值中的边不会平方增长

## 稀疏分析

SSA 上的流非敏感分析与流敏感分析等价，因此基于静态单赋值形式的分析通常又称为稀疏分析。

## 指针

一旦涉及到地址，那么 SSA 就不能用了：

```c
a = 10;
i = &a;
*i = 10;
```

解决方案：把内存位置分成两组，转换SSA的时候只转换可以被转换的组，并只对转换的组做优化
- Java：栈上的变量会被优化，堆上的变量不会被优化
- C：把变量分成 address-taken 和 top-level 两组
  + address-taken：曾经被 `&` 取过地址的变量
  + top-level：从没被 `&` 取过地址的变量

LLVM 里面会使用 memSSA，解决部分内存依赖问题。
