---
layout: "post"
title: "「PKU - Software Analysis」 05 Pointer Analysis"
subtitle: "过程内指针分析"
author: "roife"
date: 2022-05-09

tags: ["程序分析@Tags", "北大软件分析@课程相关", "课程相关@Tags", "指针分析@程序分析", "未完成@Tags", "编译@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 流非敏感的指针分析

指针分析被用来分析每个指针变量可能指向的内存位置。这里先不考虑在堆上分配的内存，不考虑struct、数组等结构，不考虑指针运算。

## Anderson 指针分析算法

### 约束

| 赋值语句 | 约束 |
|-|-|
| `a = &b` | $A \ni \\{b\\}$ |
| `a = b` | $A \supseteq B$ |
| `a = *b` | $\forall v \in B, A \supseteq V$ |
| `*a = b` | $\forall v \in A, V \supseteq B$ |

（小写字母表示变量的地址，大写字母表示指针值集合）

其他语句可以转换成这四种基本形式：`**a = *b` 等价于 `c = *b; d = *a; *d = c;`

### 约束不等式转换为方程

$$
D_{v_i} \sqsubseteq F_{v_i} (D_{v_1}, D_{v_2}, \dots D_{v_n}) \Leftrightarrow D_{v_i} = D_{v_i} \sqcap F_{v_i} (D_{v_1}, D_{v_2}, \dots D_{v_n})
$$

$$
D_{v_i} \sqsupseteq F_{v_i} (D_{v_1}, D_{v_2}, \dots D_{v_n}) \Leftrightarrow D_{v_i} = D_{v_i} \sqcup F_{v_i} (D_{v_1}, D_{v_2}, \dots D_{v_n})
$$

### 例子

```c
o = &v;
q = &p;
if (a > b) {
    p = *q;
    p = o;
}
*q = &w;
```

对应的约束：

$$
O \ni v \\
Q \ni p \\
\forall v \in Q, P \supseteq V \\
P \supseteq O \\
\forall v \in Q, V \ni w
$$

将约束转换为标准形式：

$$
P = P \cup O \cup (\bigcup_{v \in Q} V) \cup (p \in Q ? \{w\} : \emptyset) \\
Q = Q \cup \{p\} \cup (q \in Q ? \{w\} : \emptyset) \\
O = P \cup \{v\} \cup (o \in Q ? \{w\} : \emptyset) \\
$$

可以迭代计算。

每条边传递需要的复杂度为 $O(n)$（$n$ 为变量数量），边的数量为 $O(n^2)$，总复杂度为 $O(n^3)$。

一个优化：强连通子图中的每个集合必然相等。因此可以先计算强连通图，然后计算。

# 流敏感的指针分析算法

- 半格集合：指针变量到内存位置集合的映射
- 交汇操作：集合取并
- 转换函数：

| 赋值语句 | 约束 |
|-|-|
| `a = &b` | $f(V) = V[A \mapsto \\{b\\}]$ |
| `a = b` | $f(V) = V[A \mapsto B]$ |
| `a = *b` | $f(V) = V[A \mapsto \bigcup_{\forall x \in B}X]$ |
| `*a = b` | $$f(V) = \begin{cases} \forall x \in A, V[X \mapsto B] & \vert A \vert = 1 \\ \forall x \in A, V[X \mapsto X \cup B] & \vert A \vert > 1\end{cases}$$ |

在 `*a = b` 的第二种情况中，由于不能确定 `a` 指向了谁，所以只能进行 weak update；而在第一种情况中已经确定，则可以使用 strong update。

传统流敏感的指针分析算法很慢，最新工作采用了部分 SSA 来对流敏感进行加速。

# 复杂情况

## 堆上内存分配

```c
a = malloc()
```

`malloc()` 语句每次执行创造一个内存位置，可能被执行无穷次，变量个数非有限个。即可以用 `malloc()` 被调用的位置来区分不同的 `malloc()`，相同位置（例如某个循环中在不同次循环间同一位置的分配）则不区分，视为一个位置。

## struct

```c
Struct Node {
    int value;
    Node* next;
    Node* prev;
};

a = malloc();
a->next = b;
a->prev = c;
```

在 struct 中，成员也可以动态创建。

### 域非敏感分析

Field-Insensitive Analysis 指将 struct 中的所有 fields 当成一个对象。

即将上面的程序变为：

```c
a = malloc();
a = b;
a = c;
```