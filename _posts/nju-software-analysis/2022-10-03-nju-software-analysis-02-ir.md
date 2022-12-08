---
layout: "post"
title: "「NJU - Software Analysis」 02 IR"
subtitle: "中间表示"
author: "roife"
date: 2022-10-03

tags: ["程序分析@Tags", "南大软件分析@课程相关", "课程相关@Tags", "编译@Tags", "IR@编译"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# IR

通常来说，快速的类型检查会在 AST 上进行，而静态分析会在 IR 上进行（因为 AST 缺乏控制流信息）。

# 3-Address Code

三地址码是一种基础的 IR，形如下面的格式

```
x = y bop z
x = uop y
x = y
goto L
if x goto L
if x rop y goto L
```

Java 中常用的静态分析框架 Soot 用的就是一种带类型的三地址码。

## JVM 中的方法调用

- invokespecial: ctor, superclass methods, private methods（编译期确定）
- invokevirtual: virtual methods（如果是 final 修饰的方法，也是在编译期确定）
- invokeinterface: interface methods (cannot optim, checking implementation)
- invokestatic: static methods（编译期确定）
- invokedynamic: 用于动态方法

在 SOOT 里面调用的形式为 `<CLASS: METHOD_SIG>();`。

类内初始化会在 `public static void <clinit>` 中进行。

# SSA

SSA 是一种特殊的 IR，其中每个变量有1个定义。SSA 能够简化分析过程，其中的变量有着清晰的 Def-Use 信息。

# 基本块

基本块中的代码都是顺序执行的。

基本块构造算法：
- Determine the leaders in P
  + The **first instruction** in P is a leader
  + Any **target instruction** of a **jump** is a leader
  + Any instruction that **immediately follows** a **jump** is a leader
- Build BBs for P
  + A BB consists of a leader and all its subsequent instructions **until the next leader**

# CFG

控制流图以基本块为单位，能够表达程序中的控制流。

在 CFG 中，一条 A 到 B 的控制流边有两种情况：
- A 跳转到 B
- A 不以无条件跳转结尾，且 B 紧跟着 A
