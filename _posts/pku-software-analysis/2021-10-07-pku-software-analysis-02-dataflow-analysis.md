---
layout: "post"
title: "「PKU - Software Analysis」 02 Dataflow Analysis"
subtitle: "数据流分析"
author: "roife"
date: 2021-10-07

tags: ["程序分析@Tags", "北大软件分析@课程相关", "课程相关@Tags", "数据流分析@程序分析", "编译@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 抽象程序

分析程序时，需要穷举程序所有可能的执行路径，但是这是不现实的，所以需要将其映射到抽象程序。

> 将无法处理的程序映射到可处理的程序空间

- 对于程序中的分支，认为分支的两种情况都有可能到达
- 对于程序中的循环，可以当作 `goto` 加上分支的情况

这样就可以将原始程序转换为抽象程序，原始程序的执行路径一定包含在抽象程序的执行路径中，这样就可以将原始程序的问题转换为抽象程序上的问题。

直观理解看，就是在 CFG 上对程序进行分析，并且考虑程序运行的所有路径。

例如对停机问题而言，在原始程序中等价于：要求存在自然数 $n$，使程序执行路径长小于 $n$。而对于抽象程序，变成了：存在自然数 $n$，使程序所有路径长度都小于 $n$。

但是在抽象程序上只能得到问题的近似解。

> - 近似方案 1：忽略掉程序的条件判断，认为所有分支都有可能到达
> - 近似方案 2：不在路径末尾做合并，在控制流汇合的所有位置提前做合并

# 例：符号分析

> 给定一个只包含浮点数变量和常量的程序，已知输入的符号，求输出的符号

使用上一篇讲到的抽象域：
- `+ = {所有的正数}`
- `0 = {0}`
- `- = {所有的负数}`
- `? = {所有的整数和 NaN}`

对于一个给定的程序，去掉分支和循环将其转换成抽象程序。此时在程序的 $n$ 个分支上，变量的符号会有 $n$ 种可能的结果 $(v_1, v_2, \dots, v_n) \in \\{+, -, 0, ?\\}$，需要在分支的交汇处进行合并：

$$
\sqcap(v_1, v_2, \dots, v_n)
$$

在符号分析中可以定义

$$
\sqcap(v_1, v_2) =
\begin{cases}
v_1 &, v_1 = v_2 \\
? &, \operatorname{\mathtt{else}}
\end{cases}
$$

为了减少计算量，在合并结果时应该在**控制流交汇处**进行合并。

## 算法

设下面这个程序进行分析：

```c
// 一开始 x<0, y=0, z>0
x *= -100;
y += 1;
while(y < z) {
    x *= -100;
    y += 1;
}
```

这里的符号分析是一个 May 分析。
由于程序中有回边，因此需要迭代算法直到不动点。

- 令 $S = \\{(s_x, s_y, s_z) \vert s_\ast \in \\{ +, -, 0, ?, \top \\}\\}$，$\top$ 表示还没有分析
- 每个结点的值为 $S$ 的一个元素，代表对应语句执行之后的变量符号，用 $\operatorname{\mathtt{DATA}}$ 表示
- 初始值
  + $\operatorname{\mathtt{DATA}}_{\operatorname{\mathtt{entry}}} =(-, 0, +)$
  + $\operatorname{\mathtt{DATA}}_{\operatorname{\mathtt{others}}}=(\top, \top, \top)$
- 结点转换函数 $f_v : S \rightarrow S$（一个节点内的转换）
  + $f_{\operatorname{\mathtt{exit}}} = \operatorname{\mathtt{id}}$
  + $f_{\operatorname{\mathtt{others}}} = \text{根据语句进行计算}$
- $\operatorname{\mathtt{MEET}}\_v = \sqcap\_{w \in \operatorname{\mathtt{pred}}(v)} \operatorname{\mathtt{DATA}}_w$，其中 $x \sqcap \top = x$
- 结点更新运算 $S_v = f_v(\operatorname{\mathtt{MEET}}_v)$
- 如果某个结点的前驱结点发生了变化，则使用结点更新运算更新该结点的附加值
- 如果没有任何结点的值发生变化，则程序终止

结点转换运算是指**每个结点**（相当于一条语句）对结果的计算，交汇运算是在**控制流交汇点**的汇合运算。

## 算法性质

- 算法是否安全（safe）
- 算法是否保证终止（Terminating）
- 算法是否合流（Confluent）
  + 有多个结点可更新的时候，无论先更新哪个结点最后都会到达同样的结果
- Terminating + Confluent = Convergence

# 例：活跃变量分析

> 给定程序中的某条语句 `s` 和变量 `v`，如果在 `s` 执行前保存在 `v` 中的值在后续执行中还会被读取就被称作**活跃变量**

活跃变量分析会返回所有可能的活跃变量，因此是一个 May 分析。

## 算法

活跃变量为倒序查找。

- 初始值 $\operatorname{\mathtt{DATA}}_v = \\{\\}$
- 结点转换函数 $f_v(L) = (L \backslash \operatorname{\mathtt{KILL}}_v) \cup \operatorname{\mathtt{GEN}}_v$
  + $\operatorname{\mathtt{GEN}}_v = vars(v)$
  + $$
    \operatorname{\mathtt{KILL}} =
    \begin{cases}
    \{x\} & v \coloneqq x = exp; \\
    \{x\} & v \coloneqq \operatorname{\mathtt{int}}\ x; \\
    \{\} & \operatorname{\mathtt{otherwise}}
    \end{cases}
    $$
- 交汇运算 $\operatorname{\mathtt{MEET}}\_v = \cap\_{w \in \operatorname{\mathtt{succ}}(v)} \operatorname{\mathtt{DATA}}_w$
- 结点更新运算 $L_v = f_v(\operatorname{\mathtt{MEET}}v)$
- 如果某个结点的前驱结点发生了变化，则使用结点更新运算更新该结点的附加值
- 如果没有任何结点的值发生变化，则程序终止

# 数据流分析单调框架

对所有数据流分析算法的一个通用框架，通过配置框架的参数，可以导出各种类型的算法，并保证算法的安全性、终止性、收敛性。

需要抽象的内容：
- 不同算法在结点上附加的值的类型不同
- 不同算法给出的结点转换函数不同

## 数学基础

### 半格（semilattice）

> 半格是一个二元组 $(S,⊓)$，其中 $S$ 是一个集合，$\sqcap$ 是一个交汇运算，并且任意 $x, y, z \in S$ 满足
>
> - 幂等性（idempotence）：$x \sqcap x = x$
> - 交换性（commutativity）：$x \sqcap y = y \sqcap x$
> - 结合性（associativity）：$(x \sqcap y) \sqcap z = x \sqcap (y \sqcap z)$
> - 最大元：$x \sqcap \top = x$

### 偏序

> 偏序是一个二元组 $(S, \sqsubseteq)$，其中 $S$ 是一个集合，$\sqsubseteq$ 是一个定义在 $S$ 上的二元关系，并且满足以下性质：
>
> - 自反性：$\forall a \in S, a \sqsubseteq a$
> - 传递性：$\forall x, y, z \in S, x \sqsubseteq y \wedge y \sqsubseteq z \Rightarrow x \sqsubseteq z$
> - 非对称性：$x \sqsubseteq y \wedge y \sqsubseteq x \Rightarrow x = y$

**每个半格都对应了一个偏序关系**：$x \sqsubseteq y \Leftrightarrow x \sqcap y = x$

- 任意集合和并集操作组成了一个半格
  + 偏序关系为子集关系，顶元素为全集
- 任意集合和交集操作组成了一个半格
  + 偏序关系为超集关系，顶元素为空集

### 半格的性质

- 半格的笛卡尔乘积 $(S \times T, \sqcap_{xy})$ 还是半格
  + $(s_1, t_1) \sqcap_{xy} (s_2, t_2) = (s_1 \sqcap_x s_2, t_1 \sqcap_y t_2)$

- 半格的**高度**为偏序图中任意两个结点的最大距离+1（偏序关系中距离最远的两个点）
  + 符号分析中半格高度为 3
  + 活跃变量分析中半格高度为变量总数+1

![Lattice in Symbol Analysis](/img/in-post/post-software-analysis/symbol-analysis-lattice.png){:height="150px" width="150px"}

### 单调（递增）函数

> 给定一个偏序关系 $(S, \sqsubseteq)$，称一个定义在 $S$ 上的 函数 $f$ 为单调函数，当且仅当对任意 $a, b \in S$ 满足
>
> - $a \sqsubseteq b \Rightarrow f(a) \sqsubseteq f(b)$
> - 单调不说明输出和输入有偏序关系，即不是 $a \sqsubseteq f(a)$

> 设 $f(x, y) = x \sqcap y$，$(S, \sqcap)$ 是偏序关系定义的半格，则 $f(x, y)$ 单调。
>
> - 设 $x \sqcap x' = x, y \sqcap y' = y$
> - $f(x, y) \sqcap f(x', y') = (x \sqcap y) \sqcap (x' \sqcap y') = (x \sqcap x') \sqcap (y \sqcap y') = x \sqcap y = f(x, y)$
> - 所以 $f(x, y)$ 单调

- 符号分析中的加减乘除操作都是单调的（偏向于 `?`）
- 集合和交/并操作构成的半格，任意给两个集合 `GEN` 和 `KILL`，$f(S) = (S - KILL** \cap GEN$ 为单调函数

### 下界

- **下界**：给定集合 $S$，如果满足 $\forall s \in S, u \sqsubseteq s$，则称 $u$ 是 $S$ 的一个下界
- **最大下界**：设 $u$ 是集合 $S$ 的下界，给定任意下界 $u'$，如果满足 $ u' \sqsubpseteq u$，则称 $u$ 是 $S$ 的最大下界，记为 $T_S$
- $\sqcap_{s \in S} S$ 是 $S$ 的最大下界

**半格的任意子集都有最大下界**

## 数据流分析单调框架

### 组成

- 控制流图 $(V, E)$
- 有限高度的半格 $(S, \sqcap)$
- entry 的初值 $I$
- 一组单调函数，$\forall v \in V - entry, \exists f_v$

对于逆向的分析可以变换 CFG 的方向再应用框架

### 伪代码

$$
\begin{aligned}
& \operatorname{\mathtt{DATA}}_{\operatorname{\mathtt{entry}}} = I \\
& \forall v \in (V - \operatorname{\mathtt{entry}}), \operatorname{\mathtt{DATA}}_v \leftarrow \top \\
& \operatorname{\mathtt{ToVisit}} \leftarrow V - \operatorname{\mathtt{entry}} \\
& \operatorname{\mathtt{while}}\ \vert \operatorname{\mathtt{ToVisit}} \vert > 0 \\
& \qquad \operatorname{\mathtt{let}}\ v = \operatorname{\mathtt{ToVisit}}.\operatorname{\mathtt{pop}}() \\
& \qquad \operatorname{\mathtt{MEET}}_v \leftarrow \sqcap_{w \in \operatorname{\mathtt{pred}}(v)} \operatorname{\mathtt{DATA}}_w \\
& \qquad \operatorname{\mathtt{if}}\ \operatorname{\mathtt{DATA}}_v \ne f_v(\operatorname{\mathtt{MEET}}v) \\
& \qquad \qquad \operatorname{\mathtt{ToVisit}} \leftarrow \operatorname{\mathtt{ToVisit}} \cup \operatorname{\mathtt{succ}}(v) \\
& \qquad \operatorname{\mathtt{DATA}}_v \leftarrow f_v(\operatorname{\mathtt{MEET}}v)
\end{aligned}
$$

设计一个数据流分析包含下面的内容：
- 每个结点附加值的定义域
- 入口结点的初值
- 交汇函数
- 结点变换函数，通常定义为$f(D) = (D - \operatorname{\mathtt{KILL}}) \cup \operatorname{\mathtt{GEN}}$，确定 $\operatorname{\mathtt{KILL}}$ 和 $\operatorname{\mathtt{GEN}}$

需要证明如下内容：
- 在单条路径上，变换函数保证安全性
- 交汇函数对多条路径的合并方式保证安全性
- 交汇函数形成一个半格
- 半格的高度有限（通常通过结点附加值的定义域为有限集合证明）
- 变换函数均为单调函数

### 安全性

> 对控制流图上任意结点 $v_i$ 和从 $\operatorname{\mathtt{entry}}$ 到 $v_i$ 的所有可行路径集合 $P$，满足
>
> $$
> \operatorname{\mathtt{DATA}}_{v_i} \sqsubseteq \sqcap _{v_1 v_2 \dots v_i \in P} f_{v_i} \circ f_{v_{i-1}} \circ \dots \circ f_{v_1} (I_{\operatorname{\mathtt{entry}}})
> $$

直观理解：数据流分析的结构一定包含任意一条路径的结果，在关系图从初始值不断向下走。
- 在符号分析中，$\top$ 最大，数据流分析会不断偏向 $?$
- 在可用表达式中，${}$ 最大，数据流分析

关键在于数据流分析是在 CFG 交汇点进行合并的，因此会提前合并多条路径，这里需要证明提前合并不影响结果。

#### 证明

TODO

## 分配性

> $\forall v \in V, x, y \in S, f_v(x) \sqcap f_v(y) = f_v(x \sqcap y)$

**不是所有数据流分析都满足分配性**

直观理解：保证数据流分析的结果是最优结果
- 符号分析不满足分配性，令 $f_v$ 为“乘以零”，则 $f_v(+) * f_v(-) = 0 \ne f_v(+ \sqcap -) = f_v(?) = ?$
- 集合交并构成的半格，函数 $f(\operatorname{\mathtt{DATA}}) = (\operatorname{\mathtt{DATA}} - \operatorname{\mathtt{KILL}}) \cup \operatorname{\mathtt{GEN}}$ 都满足分配性
  + $f(x) \cap f(y) = (x - K) \cap G \cap (y - K) \cap G = (x - K) \cap (y - K) \cap G = (x \cap y - D) \cap G = f(x \cap y)$
  + $f(x) \cup f(y)$ 同理

当数据流分析满足分配性时，近似优化 2（交汇点合并）是等价变换。

## 收敛性

> - 不动点：给定函数 $f: S \rightarrow S$，如果 $x = f(x)$，则称 $x$ 是 $f(x)$ 的一个不动点
> - 不动点定理：给定高度有限的半格 $S, \sqcap$ 和一个单调函数 $f$，链 $T_S, f(T_S), f(f(T_S)), \dots$ 必定于有限步内收敛于 $f$ 的最大不动点
>   + $f^{i + 1}(T_S) \sqsubseteq f^i (T_S)$ 递减，又格高度有限，因此存在不动点
>   + 设存在两个不动点 $v, u \sqsubseteq T_S$，对两边同时应用不动点得 $f^n(u) \sqsubseteq f^n(T_S) = v$

在数据流分析中，算法可以看作反复应用一个函数：

$$
(\operatorname{\mathtt{DATA}}_{v_1}, \operatorname{\mathtt{DATA}}_{v_2}, \dots, \operatorname{\mathtt{DATA}}_{v_n}) \coloneqq F((\operatorname{\mathtt{DATA}}_{v_1}, \operatorname{\mathtt{DATA}}_{v_2}, \dots, \operatorname{\mathtt{DATA}}_{v_n}))
$$

根据不动点定理，数据流分析算法收敛。

# 例：可达定值分析

> 对程序中任意语句，分析运行该语句后每个变量的值可能是由哪些语句赋值的

- 正向分析
- 半格元素:集合的序列 `[{}]`，序列每个位置的集合代表一个变量的定值语句序号集合
- 交汇操作：$\bigcup$
- 变换函数：
  - 对于赋值语句 $v = x$
    + $\operatorname{\mathtt{KILL}} = \\{\text{当前集合中对 $v$ 赋值的语句}\\}$
    + $\operatorname{\mathtt{GEN}} = \\{\text{当前语句}\\}$
  - 对于其他语句
    + $\operatorname{\mathtt{KILL}} = \operatorname{\mathtt{GEN}} = \\{\\}$

# 例：可用表达式

> 对程序中任意语句，分析运行该语句后每个变量的值可能是由哪些语句赋值的

- 正向分析
- 半格元素:集合的序列 `[{}]`，序列每个位置的集合代表一个变量的定值语句序号集合
- 交汇操作：$\bigcap$
- 变换函数：
  - 对于赋值语句 $v = x$
    + $\operatorname{\mathtt{KILL}} = \\{\text{当前集合中包含变量 $v$ 的表达式}\\}$
    + $\operatorname{\mathtt{GEN}} = \\{\text{当前语句的表达式}\\}$
  - 对于其他语句
    + $\operatorname{\mathtt{KILL}} = \operatorname{\mathtt{GEN}} = \\{\\}$

# 例：区间分析

> 求某个变量取值的上界和下界

例如 $a \in [0, +\infty]$

# Widening & Narrowing

## Widening

格的高度太高时，需要走很多步才能收敛。此时可以用 widening 降低结果的精度加快收敛速度：
- 基础Widening：降低格的高度
- 一般Widening：根据变化趋势快速猜测一个结果

### 基础 Widening

在转换函数中进一步缩小答案的值域，例如用一个集合泛化分析结果。

例如对于区间分析问题：
- 定义有限集合 $B = \\{ -\infty, 10, 20, 50, 100, \infty \\}$
- 定义一个单调函数 $\omega ([l, h]) = [ \max\\{i \in B \vert  \le i\\}, min\\{[i \in B \vert h \le i]\\}]$
- 令新的转换函数为 $\omega \circ f$

基础 widening $\omega$ 单调，并且结果比原来小，所以能保证安全性和收敛性。

### 一般 widening

一般 widening 会同时参考更新前后的值来预测最终会收敛的值：
- 原始更新语句
  + $\operatorname{\mathtt{DATA}}\_v \leftarrow f\_v(\operatorname{\mathtt{MEET}}_v)$
- 引入 widening 算子 $\nabla$
  + $\operatorname{\mathtt{DATA}}\_v \leftarrow \operatorname{\mathtt{DATA}}_v \nabla f\_v(\operatorname{\mathtt{MEET}}_v)$

例如对于区间分析问题：
- $[a, b] \nabla \top = [a, b]$，$\top \nabla [c, d] = [c, d]$
- $[a, b] \nabla [c, d] = [x, y]$
  + $x = \begin{cases} a &, c \ge a \\\\ -\infty &, c < a \end{cases}$
  + $y = \begin{cases} d &, d \le b \\\\ +\infty &, b > d \end{cases}$

一般 widening 的安全性和收敛性不一定能保证：
- 如果 $x \nabla y \sqsubseteq y \wedge x \nabla y \sqsubseteq x$ 则可以保证安全性
- 没有一般的方法可以保证收敛性（有可能不是单调，在一些点上值不变）
  + $[1, 1] \nabla [1, 2] = [1, +\infty]$，$[1, 2] \nabla [1, 2] = [1, 2]$
  + 由于一般 widening 遇到缩小的情况会直接变成 $\infty$，因此节点更新的次序也会对算法的结果产生影响（不同的次序让放大缩小的次序也发生了变化，而一旦变成 $\infty$ 就不能挽救回来），所以算法得出的结果可能不确定

## Narrowing

Widening 已经算出结果后继续用**原始转换函数**修正。

- 原始更新语句
  + $\operatorname{\mathtt{DATA}}\_v \leftarrow f\_v(\operatorname{\mathtt{MEET}}_v)$
- 引入 narrowing 算子 $\Delta$
  + $\operatorname{\mathtt{DATA}}\_v \leftarrow \operatorname{\mathtt{DATA}}_v \Delta f\_v(\operatorname{\mathtt{MEET}}_v)$

### 安全性

可以把聚类分析看作一个函数 $F$
- 设原数据流分析的函数为 $F$，收敛于 $I_F$
- 设经过 widening 的函数为 $G$，收敛于 $I_G$
- $I_F \sqsupseteq I_G$，$F \sqsupseteq G$
- 则 $I_F = F(I_F) \sqsupseteq F(I_G) \sqsupseteq G(I_G) = I_G$
- 则 $I_F \sqsupseteq F^k(I_G) \sqsupseteq I_G$

说明 narrowing 的结果不仅安全，而且更加精确（$F_k(I_G) \sqsupseteq I_G$）。

Narrowing 也不能保证快速收敛，即不知道使用 narrowing 的次数（$k$）
- 因此和 widening 一样引入 narrowing 算子解决其收敛性的问题

### Narrowing 算子

例如对于区间分析问题：
- $[a, b] \Delta [c, d] = [x, y]$
  + $x = \begin{cases} a &, a \ne -\infty \\\\ c &, a = -\infty \end{cases}$
  + $y = \begin{cases} b &, b \ne +\infty \\\\ d &, b = +\infty \end{cases}$
  + 即已经收敛到的整数不改动，只重新计算被 widening 扩展到无穷大的部分


Narrowing 算子的安全性和收敛性也不一定能保证：
- 如果 $x \Delta y \sqsubseteq y$ 则可以保证安全性
- 没有一般的方法可以保证收敛性

# 逻辑编程语言：Datalog

Datalog 是 Prolog 的一个子集，通常用来写数据流分析。简单语法为：

```prolog
% 表示 p2 + p3 能推出 p1
p1(var_or_const_list) :- p2(var_or_const_list), p3(var_or_const_list)
```

例如一个正向数据流分析标准型（并集）：

```prolog
% V表示结点，D表示一个集合中的元素
data(D, V) :- gen(D, V)
data(D, V) :- edge(V’, V), data(D, V’), not_kill(D, V)
data(d, entry) // if d∈I
```

如果是取交集，则写作：

```prolog
data(D, V) :- gen(D, V)
data(D, v) :- data(D, v1), data(D, v2), ..., data(D, vn), not_kill(D, v) % v1,v2,...vn是v的前驱结点
data(d, entry) % if d
% 更好的方法是取补集，将交集转换成并集
```

## Datalog$\neg$

`not_kill` 构造效率很低，那么能不能引入 $\neg$？

不能，因为会引入悖论：

```prolog
p(x) :- not p(x)
% 而且会导致函数不再是单调的
```

Datalog 引入了**分层**（stratified），规定*谓词上的任何环状依赖不能包含否定规则*。

例如 `p1 :- p2`，`p2 :- p1` 构成了环状依赖，此时在环状依赖上不能有 $\neg$。

## 常用引擎

- Souffle
- LogicBlox
- IRIS
- XSB
- Coral

# 方程求解

数据流分析的传递函数和 $\sqcap$ 操作定义了一组方程，数据流分析即为求解该方程的最大解。
- 传递函数和⊓操作表达了该分析的安全性条件，所以该方程的解都是安全的
- 最大解是最有用的解

$$
\begin{aligned}
& D_{v_1} = F_{v_1}(D_{v_1}, D_{v_2}, \dots, D_{v_n}) \\
& D_{v_2} = F_{v_2}(D_{v_1}, D_{v_2}, \dots, D_{v_n}) \\
& \dots \\
& D_{v_n} = F_{v_n}(D_{v_1}, D_{v_2}, \dots, D_{v_n})
\end{aligned}
$$

其中

$$
\begin{aligned}
& F_{v_1}(D_{v_1}, D_{v_2}, \dots, D_{v_n}) = f_{v_1}(I) \\
& F_{v_i}(D_{v_1}, D_{v_2}, \dots, D_{v_n}) = f_{v_i}(\sqcap_{j \in \operatorname{\mathtt{pred}}(i)}D_{v_j})
\end{aligned}
$$

数理逻辑中称解此类方程的算法为 **Unification** 算法，对于单调函数和有限格，标准的 Unification 算法就是数据流分析算法：
- 从 $(I, \top, \top, \dots, \top)$ 开始反复应用 $F_{v_1}$ 到 $F_{v_n}$，直到达到不动点
- 增量优化：每次只执行受到影响的 $F_{v_i}$

# 敏感性

抽象过程中考虑的属性越多，精度越高，速度越慢。

敏感性 = 考虑了某项信息

- 流敏感性 flow-sensitivity
- 路径敏感性 path-sensitivity
- 上下文敏感性 context-sensitivity
- 字段敏感性 field-sensitivity

## 流非敏感分析

- **流非敏感分析（flow-insensitive analysis）**：如果把程序中语句*随意交换位置*（即：改变控制流），如果分析结果*始终不变*，则该分析为流非敏感分析
- **流敏感分析**：程序语句随意交换位置后分析结果改变

**数据流分析通常为流敏感的**

流非敏感分析不考虑位置，直接用所有位置的语句更新，例如：

```c
a=100;
if(a>0) a=a+1;
```

$$
a = a \sqcap \operatorname{\mathtt{+}} \sqcap a + \operatorname{\mathtt{+}}
$$

虽然流非敏感分析的精度更低，但是时间复杂度也更低。下面以活跃变量分析为例（语句数为 $n$，程序中变量个数为 $m$）：
- 流非敏感的活跃变量：时间复杂度为 $O(nm)$，空间复杂度为 $O(m)$
- 流敏感的活跃变量分析：格的高度为 $O(m)$，时间复杂度为 $O(nm^2)$，空间复杂度为 $O(nm)$

流非敏感分析可以用于 SSA 分析。

## 路径敏感性

- 路径非敏感分析：不考虑程序中的路径可行性，忽略分支循环语句中的条件
- 路径敏感分析：考虑程序中的路径可行性，只分析可能的路径

例如在区间分析中，路径敏感性会影响分析结果：

```c
// 假设输入区间为 (5, 10]
int f(int x){
  if (x > 5) x = 10;
  return x;
}
```

- 如果使用路径非敏感的区间分析，得到 $x \in (5, 10]$
- 如果使用路径敏感的区间分析，得到 $x \in [10, 10]$

关键在于丢失了分支的信息，实际上并不是两个分支都会走的。

### assert

可以考虑给每条分支添加 `assert` 语句，负责过滤掉多余的状态。

```c
// 假设输入区间为 (5, 10]
int f(int x){
  if (x > 5) {
    assert(x > 5);
    x = 10;
  } else {
    assert(x <= 5);
  }
  return x;
}
```

同时为 `assert` 设置转换函数：
- 在第一条分支中，$f_{\operatorname{\mathtt{assert}}}(x) = x \in x \cup (5, \infty) = (5, 10]$
- 在第二条分支中，$f_{\operatorname{\mathtt{assert}}}(x) = x \in x \cup (-\infty, 5] = \emptyset$
- 此时在分支合并处可以得到正确的区间结果

另一个例子是关于循环的：

```c
x=1;
while (x < 100) {
  x++;
}
```

可以改写成

```c
x=1;
while (x < 100) {
  assert(x < 100);
  x++;
}

assert(x >= 100);
```

此时使用 widening 和 narrowing 就可以得到更加精确的结果。

### 路径敏感的优缺点

- 优点：完全兼容已有数据流分析框架
- 缺点：很多条件类型无法写出过滤函数，且无法精准判断

