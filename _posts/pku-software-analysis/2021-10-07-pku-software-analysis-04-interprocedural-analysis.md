---
layout: "post"
title: "「PKU - Software Analysis」 04 Interprocedural Analysis"
subtitle: "过程间分析"
author: "roife"
date: 2021-10-10

tags: ["程序分析@Tags", "北大软件分析@课程相关", "课程相关@Tags", "程序分析@Tags", "编译@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

过程间分析指考虑多个函数/过程之间的调用，或者 C/C++ 中的链接时分析。

# 基本思路

1. 对不同过程采用不同抽象域
2. 在调用和返回的时候添加结点来转换信息

例如过程 `A()` 调用过程 `B()`，则会把 `A()` 调用时的信息传入 `B()`，并把 `B()` 的信息传回 `A()`。注意，`B()` 仍然只会被分析一次，即如果由多个地方都调用了 `B()`，那么，会将所有信息全部送入 `B()` 一起分析。这样的好处是能处理递归问题。

## 问题

### 全局变量

全局变量需要添加到对其进行读写的子过程和调用这些子过程的过程中（否则离开这个子过程后，全局变量的信息就丢了，而后面可能再次用到这些信息）。

此时会带来很大的开销。

### 精度损失

多个程序调用一个子程序时，输入的信息会被汇总一起分析，此时分析结果会产生精度问题。

例如对于一个常量分析程序（判断在某个程序点某个变量的值是否是常量）：

```c
int id(int a) { return a; }

int main() {
    int x = id(100);
    int y = id(200);
}
```

- 过程内分析不精确的条件：两条互斥的路径都被执行
- 过程间分析不精确的条件：一个过程被调用两次（更加常见）

# Context-sensitivity

上面讲的都是上下文非敏感分析（Context-insensitive analysis），在过程调用的时候忽略调用的上下文。而 Context-sensitivity 可以缓解精度问题。

## 基于克隆的上下文敏感分析

Clone-based Context-Sensitive Analysis。

即调用函数时给每个函数创建一个单独的上下文环境，而不是和前面一样把所有信息汇总到子过程的开头一起分析。

例如 `A()` 调用 `B()`，`C()` 调用 `B()`，则将 `B()` 分别复制两份变成 `B1()` 和 `B2()` 到 `A()` 与 `C()` 中。

### 问题

1. 指数爆炸：在深层的调用栈中重复调用一些函数，会进行大量的复制（问题存在但是不致命）
2. 无法处理递归（导致分析无法进行）

### 解决方案

只展开固定层数。

![](/img/in-post/post-software-analysis/interprocedure-analysis-clone-depth-one.png){:height="600px" width="600px"}

![](/img/in-post/post-software-analysis/interprocedure-analysis-clone-depth-two.png){:height="600px" width="600px"}

## 其他的上下文敏感分析

- 基于函数名字的上下文：把上面的基于调用位置区分的上下文分析变成基于函数名字的上下文分析。例如 `2::3` 变成 `fib::fib`。不如调用位置精确，但能减少复制量
- 基于对象类型的类型的上下文
  + 对于多态的对象，对于每种可能的子类型使用不同的上下文
  + 对于重载的方法，对于每种重载的方法使用不同的上下文
- 基于系统状态的上下文
  + 根据分析需要，对系统的当前状态进行分类
  + 当函数以不同状态调用时，对函数复制

## 克隆与过程内分析

以分支为例。先前考虑过程内分析时，会默认走所有的分支路径，但是如果存在条件互斥的情况，可以做出更加精确的分析：

```c++
if(c1)
    x();
else
    y();

z();

if (c2) // c1 and c2 == 0
    m();
else
    n();
```

考虑到 `c1` 和 `c2` 互斥，那么只可能有两种可能的路径：`x z n` 或 `y z m`。

此时可以用克隆实现更精确的分析：

```c++
if(c1) {
    x();
    z();
    if (c2)
        m();
    else
        n();
} else {
    y();
    z();
    if (c2)
        m()
    else
        n();
}
```

对于其他的结构也可以利用克隆做更精确的分析：
- 循环：可以展开 $k$ 层，这样对于前 $k$ 层会有比较精确的结果
- 系统状态：根据对系统状态的分类同样可以在语句级别而不是过程级别进行复制

## 内联与克隆

通过函数内联，将过程间分析转为过程内分析，实现克隆的效果。

# 精确的上下文敏感分析

- 考虑最近任意多次调用的上下文
- 对于任意分析中考虑的路径，路径中的调用边和返回边全部匹配（称为可行路径）

历史上提出过精确上下文敏感分析方法：
- Functional
- Dataflow Facts-based Summary
- CFL-reachability

在面向对象程序中，上下文敏感分析比上下文非敏感分析精确很多。

# CFL-reachability

## Dyck-CFL

Dyck-CFL 是 CFL 的一个子类，由带标号的括号组成。显然在 Dyck 中，括号都是匹配的。

$$
\begin{aligned}
S ::= {}\ &\ \{_1\ S\ \}_1 \\
      | &\ \{_2\ S\ \}_2 \\
      | &\ \dots \\
      | &\ S\ S \\
      | &\ \varepsilon
\end{aligned}
$$

在进行上下文敏感性分析时，可以给系统中的每一处调用分配唯一一对括号，如果路径上的符号符合 Dyck 的文法，那么是可行路径。

![Dyck CFL in Interprocedure Analysis](/img/in-post/post-software-analysis/dyck-cfl-interprocedure-analysis.png){:height="500px" width="500px"}

## 数据流分析分配性的推论

对于一个满足分配性的数据流分析 $X$，其 $\mathtt{entry}$ 节点的初值是 $I^X$。

令 $Y$ 和 $Z$ 是仅有初值不同的数据流分析，其初值分别为 $I^Y$ 和 $I^Z$，且 $I^X = I^Y \sqcap I^Z$。

设 $\mathtt{DATA}^X_v$ 为通过 $X$ 分析得到的 $v$ 的初值，则 $\mathtt{DATA}^X_v = \mathtt{DATA}^Y_v \sqcap \mathtt{DATA}^Z_v$。

例子：

要对 $(a, b) = (+, +)$ 进行符号分析，可以将其拆成 $(a, b') = (+, ?)$ 和 $(a', b) = (?, +)$ 分别进行分析，最后将结果进行汇聚。

## 转换函数与图可达性

对于可分配转换函数 $f(X) = (X \backslash \{a\}) \cup \{c\}$。这个函数可以表达成一个图：

![Transition Function in Graph](/img/in-post/post-software-analysis/interprocedure-analysis-transition-function-in-graph.png){:height="150px" width="150px"}

此时可以利用图的可达性计算转换函数的结果：例如求 $f(\{a, b\})$，可以从图上分别以 $a$ 和 $b$ 为起点，取其可以到达的边，取并集（或交集）即为转换函数的结果。

## 未初始化变量分析

![](/img/in-post/post-software-analysis/uninitialized-variables-analysis.png){:height="700px" width="700px"}

如图是一个对于“未初始化变量”的分析。转移函数为

$$
f(X) =
\begin{cases}
& X \backslash \{a\} & \text{$a$ is initialized} \\
& X \cup \{b\} & \text{$b := \mathtt{expr}$ and $\mathtt{expr} \wedge X \ne \emptyset$}
\end{cases}
$$

其中每一条语句都可以**独立**连边。

例如对于语句 `n1: READ(x)` 初始化了 $x$，则不连 $x$；对于语句 `n6: a:=a-g` 表示如果 $g$ 没有初始化，那么 $x$ 和 $g$ 都算未初始化。

要考察到达某个点时某个变量是否被初始化，只要从 $\mathtt{entry}$ **能否走到某这点的变量**。例如 $\mathtt{entry} \rightarrow n6$ 的路线中，$x$ 不可达，因此 $x$ 被初始化了。

图的每一条路径上都有一个标签。对于任意一条路径，只有其走过的标签排列符合 Dyck CFL，那么这条路径才是合法的。这样就可以从中筛选出合法的路径，并且只考虑这些合法的路径。如果存在这样的一条合法路径，那么说明这个变量是未初始化的。

## 上下文无关语言可达性问题

按照上面的例子，上下文敏感分析可以转换成一个图上的自动机问题：

> 给定一个图，其中每条边上有标签。给定一个用 CFL 描述的语言 L，对于图中任意结点 $v_1$、$v_2$，确定是否存在从 $v_1$ 到 $v_2$ 的路径 $p$，使得该路径上的标签组成了 $L$ 中的句子。

### 解决方案

首先重写 Dyck CFL 的文法：

$$
\begin{aligned}
S ::= {}\ &\ \{_1\ E_1 \\
      | &\ \{_2\ E_2 \\
      | &\ \dots \\
      | &\ S\ S \\
      | &\ \varepsilon \\
E_1 ::= {}& S\ \}_1 \\
E_2 ::= {}& S\ \}_2 \\
\end{aligned}
$$

此时所有的推导都只有两个符号，因此可以将其转换成三种模式：

如图，三种图代表三种模式。其中实线是原有的符号，虚线是根据模式添加的符号。只要按照算法不断加边即可。

![Graph Construction](/img/in-post/post-software-analysis/interprocedure-analysis-graph-construction.png){:height="500px" width="500px"}

### 一些性质

- Soundness： 给定任意控制流图上的可行路径，该路径上算出的结果一定包含在 CFL-Reachability 算出的结果中
- Precision：给定任意 $n$，以前 $n$ 次调用位置作为上下文的基于克隆的分析所产生的结果一定包括 CFL-Reachability 分析所产生的结果

## IFDS

可以用 CFL 可达性解决的问题称为 **IFDS 问题**。
- Interprocedural
- Finite（图的结点数量不能是无限的）
- Distributive
- Subset problems

# 过程间分析加速技术

## 目前存在的问题

- 无效计算：一般只关心从起始结点开始的可达性，CFL 求解算法都会计算过程内部的可达性
- 重复计算：一条边可能从几个不同途径添加，导致重复计算

## 基于动态规划的加速技术

## 基于函数摘要的加速技术