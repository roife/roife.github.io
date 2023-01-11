---
layout: "post"
title: "自然数"
subtitle: "Natural Numbers"
author: "roife"
date: 2022-01-18

tags: ["代数@数学", "数学@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 自然数

## 皮亚诺自然数公理

1. 0 是自然数
2. 每个自然数都有它的下一个自然数，称为它的后继
3. 0 不是任何自然数的后继
4. 不同的自然数有不同的后继数
5. 如果自然数的某个子集包含 0，并且其中每个元素都有后继元素。那么这个子集就是全体自然数

这五条规则可以用符号表示：
1. $0 \in \mathbb{N}$
2. $\forall n \in \mathbb{N}, \exists n' \in \mathbb{N}$
3. $\forall n \in \mathbb{N}, n' \ne 0$
4. $\forall n, m \in \mathbb{N}, n' = m' \Rightarrow n = m$
5. $\forall S \subseteq \mathbb{N}, (0 \in S \wedge (\forall n \in S \Rightarrow n' \in S)), S = \mathbb{N}$

- 第三条公理用来排除 $\\{0 \rightarrow 1, 1 \rightarrow 2, 2 \rightarrow 0\\}$ 的情况；
- 第四条公理用来排除 $\\{0 \rightarrow 1, 1 \rightarrow 1\\}$ 的情况；
- 第五条公理用来排除 $\\{0, 0.5, 1, 1.5, \dots\\}$ 的情况

```haskell
data Nat = zero | succ Nat
```

## `foldn`

定义 $n = \mathtt{foldn} (\mathtt{zero}, \mathtt{succ}, n)$，即

$$
\mathtt{foldn} (z, f, 0) = z \\
\mathtt{foldn} (z, f, n') = f(\mathtt{foldn} (z, f, n))
$$

`foldn` 可以用于递归运算，利用 Curry-ing 还可以简化掉这个组合子的第三个参数。在利用 `foldn` 进行运算时，有一个技巧：利用元组存储中间值。

例如定义阶乘运算：

$$
c = (0, 1) \\
h(m, n) = (m', m' * n) \\
\mathtt{fact} = \mathtt{2nd} \circ \mathtt{foldn}(c, h)
$$

## 列表

```haskell
data List A = nil | cons(A, List A)
```

可以发现列表和自然数的定义非常相似。可以定义列表的连接操作：

$$
\mathtt{nil} + y = y \\
\mathtt{cons}(a, x) + y = \mathtt{cons}(a, x + y)
$$

同样可以定义 `foldr`，它会从右向左对元素进行操作：

$$
\mathtt{foldr}(c, h, \mathtt{nil}) = c \\
\mathtt{foldr}(c, h, \mathtt{cons}(a, x)) = h(a, \mathtt{foldr}(c, h, x))
$$

用 `foldr` 可以定义 `filter` 与 `map`：

$$
\mathtt{filter}(p) = \mathtt{foldr}(\mathtt{nil}, (p \circ \mathtt{1st} \mapsto \mathtt{cons}, \mathtt{2nd}))
$$

此处的 $\mapsto$ 为麦卡锡条件形式，$(p \mapsto f, g) \Leftrightarrow \mathtt{if}\ p(x)\ \mathtt{then}\ f(x)\ \mathtt{else}\ g(x)$

$$
\mathtt{map}(f) = \mathtt{foldr}(\mathtt{nil}, \mathtt{cons} \circ \mathtt{first}(f)) \\
\mathtt{first}(f, (x, y)) = (f (x), y)
$$

## 二叉树

```haskell
data Tree A = nil | node (Tree A, A, Tree A) -- A  为类型
```

同样可以定义 `foldt`：

$$
\mathtt{foldt}(f, g, c, \mathtt{nil}) = c \\
\mathtt{foldt}(f, g, c, \mathtt{node}(l, x, r)) = g(\mathtt{foldt}(f, g, c, l), f(x), \mathtt{foldt}(f, g, c, r))
$$

其中各个函数的类型为：
$$
\begin{aligned}
& f : A \rightarrow B \\
& \mathtt{foldt} : \mathtt{Tree}\ A \rightarrow B \\
& g : B \rightarrow B \rightarrow B \rightarrow B
\end{aligned}
$$

根据 `foldt` 可以定义 `mapt`：

$$
\mathtt{mapt}(f) = \mathtt{foldt}(f, \mathtt{node}, \mathtt{nil})
$$

利用 `List`，还可以定义多叉树和对应的 `foldm` 运算：

```haskell
data MTree A = nil | node (A, List (MTree A))
```

$$
\mathtt{foldm}(f, g, c, nil) = c \\
\mathtt{foldm}(f, g, c, \mathtt{node}(x, ts)) = \mathtt{foldr}(g(f (x), c), h, ts) \\
h(t, z) = \mathtt{foldm}(f, g, z, t)
$$
