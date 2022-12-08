---
layout: "post"
title: "「NJU - Software Analysis」 01 Introduction"
subtitle: "Soundness 与 Completeness"
author: "roife"
date: 2022-10-03

tags: ["程序分析@Tags", "南大软件分析@课程相关", "课程相关@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# PL 领域的分类

**Programming Languages**
- Theory: Language design, Type system, Semantics and logics ...
- Environment: Compilers, Runtime system ...
- Application: Program analysis, Program verification, Program synthesis ...

# Static Analysis

> **Static analysis** analyzes a program P to reason about its behaviors and determines whether it satisfies some properties **before** running P.

# Rice's Theorem

> Any **non-trivial** property of the behavior of programs in a recursively enumerable language is undecidable.

这里的 non-trivial property 可以看作是“the properties related with run-time behaviors of programs”。

# Soundness & Completeness

- Soundness：对程序进行了 over-approximate（过拟合），不会漏报，但是有 false positives（误报）
- Completeness：对程序进行了 under-approximate（欠拟合），不会误报，但是有 false negatives（漏报）

![Soundness and Completeness](/img/in-post/post-nju-software-analysis/soundness-and-completeness.png){:height="400px" width="400px"}

静态分析通常需要在保证 soundness 的前提下，去平衡精度和分析速度。

# May/Must Analysis

> Outputs information that **may/must** be true For may analysis, over-approximation is safe; for must analysis, under-approximation is safe.

大部分时候会用 May Analysis，但是有时候也会用到 Must Analysis（比如做优化的时候需要使用 Must 别名分析，此时需要确保分析出来的别名一定是正确的）。
