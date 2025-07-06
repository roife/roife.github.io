+++
title = "[计算模型] 01 递归函数"
author = ["roife"]
date = 2024-03-02
series = ["Introduction to models of computation"]
tags = ["计算理论"]
draft = false
+++

## 数论函数 {#数论函数}


### 常用函数 {#常用函数}

算术差函数 \\( \operatorname{\mathrm{sub}}: \mathbb{N} \times \mathbb{N} \rightarrow \mathbb{N} \\) 定义为 \\(\operatorname{\mathrm{sub}}(x, y) = x \dot{-} = \left\\{ \begin{array}{ll} 0, & \operatorname{if} \\, x < y, \\\ x-y, & \operatorname{if} \\, x \geq y. \end{array} \right.\\)

绝对差函数 \\( \operatorname{\mathrm{diff}}: \mathbb{N} \times \mathbb{N} \rightarrow \mathbb{N} \\) 定义为 \\(\operatorname{\mathrm{diff}}(x, y) = x \ddot{-} = |x - y|\\).

数论函数 \\( N: \mathbb{N} \rightarrow \mathbb{N} \\) 定义为 \\( N(x) = \left\\{ \begin{array}{ll} 0, & \operatorname{if} \\, x \neq 0, \\\ 1, & \operatorname{if} \\, x = 0. \end{array} \right.\\)

数论函数 \\( N^2: \mathbb{N} \rightarrow \mathbb{N} \\) 定义为 \\( N^2(x) = \left\\{ \begin{array}{ll} 0, & \operatorname{if} \\, x = 0, \\\ 1, & \operatorname{if} \\, x \neq 0. \end{array} \right.\\)

<div class="definition">

**(有界迭加算子)**

设 \\( k \in \mathbb{N}, f: \mathbb{N}^{k+1} \to \mathbb{N} \\) 的 \\( k+1 \\) 元函数是数论全函数，函数 \\( f \\) 的**有界迭加（bounded sum）** \\(\sum\_{i=0}^{n} [f(i, \vec{x})] \\) 是 \\( k+1 \\) 元数论全函数 \\( g: \mathbb{N}^{k+1} \to \mathbb{N} \\)，定义为

\\[
g(n, \vec{x}) = f(0, \vec{x}) + f(1, \vec{x}) + \cdots + f(n, \vec{x}).
\\]

\\( \sum [ \cdot ] \\) 称为迭加算子，且称 \\( g(n, \vec{x}) = \sum\_{i=0}^{n} [f(i, \vec{x})] \\) 由 \\( f \\) 经过有界迭加算子而得。

</div>

<div class="definition">

**(有界迭乘算子)**

设 \\( k \in \mathbb{N}, f: \mathbb{N}^{k+1} \to \mathbb{N} \\) 的 \\( k+1 \\) 元函数是数论全函数，函数 \\( f \\) 的**有界迭乘**（bounded product） \\( \prod\_{i=0}^{n} [f(i, \vec{x})] \\)，这是一个 \\(k+1\\) 元数论全函数 \\(h: \mathbb{N}^{k+1} \to \mathbb{N}\\)，定义如下：

\\[
h(n, \vec{x}) = f(0, \vec{x}) \cdot f(1, \vec{x}) \cdot \cdots \cdot f(n, \vec{x}).
\\]

这里，\\( \prod [\cdot] \\) 表示迭乘算子，且称 \\( h(n, \vec{x}) = \prod\_{i=0}^{n} [f(i, \vec{x})] \\) 由 \\( f \\) 经过有界迭乘算子而得。

</div>

<div class="definition">

**(有界 \\(\mu\\)-算子)**

设 \\( k \in \mathbb{N} \\), \\( f: \mathbb{N}^{k+1} \rightarrow \mathbb{N} \\) 为 \\( k+1 \\) 元数论全函数，\\( \mu x \le n. [f(x, \vec{y})] \\) 为 \\( k \\) 元 \\( 1 \\) 算论全函数 \\( g: \mathbb{N}^k \rightarrow \mathbb{N} \\), 定义为

\\[g(n, \vec{y}) = \begin{cases}
\min \\\{ x : 0 \le x \le n \land f(x, \vec{y})=0 \\\} , & \exists 0 \le x \le n. f(x, \vec{y}) = 0, \\\\
n, & \text{else}.
\end{cases}
\\]

其中 \\( \mu x \le n. [f(x, \vec{y})] \\) 有时也记作 \\( \min x \le n. [f(x, \vec{y})] \\). \\( \mu x \le n. [ \cdot ] \\) 称为有界 \\( \mu \\)-算子。且称 \\(g(n, \vec{y}) = \mu x \le n. [f(x, \vec{y})]\\) 由 \\(f\\) 经有界 \\(\mu\\)-算子而得。

</div>

<div class="definition">

**(有界 \\(\operatorname{\mathrm{max}}\\) 算子)**

设 \\( k \in \mathbb{N} \\), \\( f: \mathbb{N}^{k+1} \rightarrow \mathbb{N} \\) 为 \\( k+1 \\) 元数论全函数，\\( \text{max} \\, x \le n. [f(x, \vec{y})] \\) 为 \\( k \\) 元 \\( 1 \\) 算论全函数 \\( g: \mathbb{N}^k \rightarrow \mathbb{N} \\), 定义为

\\[g(n, \vec{y}) = \begin{cases}
\max \\\{ x : 0 \le x \le n \land f(x, \vec{y})=0 \\\}, & \exists 0 \le x \le n. f(x, \vec{y}) = 0, \\\\
0, & \text{else}.
\end{cases}
\\]

其中 \\( \operatorname{\mathrm{max}} \ x \le n. [f(x, \vec{y})] \\) 有时也记作 \\( \max x \le n. [f(x, \vec{y})] \\). \\( \operatorname{\mathrm{max}} \ x \le n. [ \cdot ] \\) 称为有界max算子。且称 \\(g(n, \vec{y}) = \operatorname{\mathrm{max}} \\, x \le n. [f(x, \vec{y})]\\) 由 \\(f\\) 经有界 \\(\operatorname{\mathrm{max}}\\) 算子而得。

</div>

有界 \\(\mu\\)-算子寻找的是使得 \\(f(x, \vec{y})=0\\) 的最小的 \\(x\\) 值，而有界max算子寻找的是这样的最大 \\(x\\) 值。如果没有任何\\(x\\)值使得\\(f(x, \vec{y})=0\\)，那么分别返回终止的边界。


### IF {#if}

<div class="definition">

**(数论函数)**

设 \\( \mathbb{N} = \\\{ 0, 1, 2, 3, \dots \\\} \\) 为全体自然数之集。

若 \\(f : \mathbb{N}^{k} \rightarrow \mathbb{N}\\)，\\( k \in \mathbb{N}^{+ }\\) 为全函数，则 \\( f \\) 被称为 \\( k \\) 元数论全函数（total number-theoretic function），简称数论函数（number-theoretic function）。若 \\(f \\) 为函数且 \\( \operatorname{\mathrm{dom}}(f) \subseteq \mathbb{N} \\), \\( \operatorname{\mathrm{ran}}(f) \subseteq \mathbb{N} \\)，则 \\(f \\) 被称为部分数论函数（partial number-theoretic function）。

</div>

<div class="definition">

**(本原函数)** 以下三类数论函数被称为**本原函数（initial function）**：

-   零函数 \\( Z : \mathbb{N} \rightarrow \mathbb{N} \\)，\\( \forall z \in \mathbb{N} . Z(z) = 0 \\)；
-   后继函数 \\(S : \mathbb{N} \rightarrow \mathbb{N}\\)，\\(\forall z \in \mathbb{N} . S(z) = z + 1\\)；
-   投影函数族 \\(P^n\_{i} : \mathbb{N}^n \rightarrow \mathbb{N}\\)，\\(\forall x\_{1}, \dots, x\_{n} \in \mathbb{N}\\)，其中 \\(n \in \mathbb{N}^+ \wedge 1 \leq i \leq n\\)，则 \\(P^{n}\_{i}(x\_{1}, \dots, x\_{n}) = x\_{i}\\)。

本原函数类记作 \\(\mathcal{IF}\\)。

</div>

<div class="definition">

设 \\(n \in \mathbb{N}^+\\)，可以将序列 \\(x\_1, x\_2, \dots, x\_n\\) 简记为 \\(\vec{x}\\)。

</div>

<div class="definition">

**(函数的复合)**

设 \\( m, n \in \mathbb{N}^{+} \\)，\\(f : \mathbb{N}^{m} \rightarrow \mathbb{N} \\)，\\( g : \mathbb{N}^{n} \rightarrow \mathbb{N} \\)，其中 \\( i = 1, 2, \dots, m \\)。函数 \\( f \\) 和 \\(g\_{1}, g\_{2}, \dots, g\_{m}\\) 的复合 \\(\operatorname{\mathrm{Comp}}^{n}\_{m}[f, g\_{1}, g\_{2}, \dots, g\_{m}]\\) 为 \\( n \\) 元数论函数 \\(h : \mathbb{N}^{n} \rightarrow \mathbb{N}\\)，定义为

\\[h(\vec{x}) = f(g\_{1}(\vec{x}), g\_{2}(\vec{x}), \dots, g\_{m}(\vec{x})).\\]

若 \\( m = 1 \\)，则 \\( \operatorname{\mathrm{Comp}}^{n}\_{1}[f, g] \\) 可简记为 \\( f \circ g \\)。

</div>


### BF {#bf}

<div class="definition">

**(基本函数)**

基本函数（basic functions）类 \\(\mathcal{BF}\\) 是满足以下条件的最小函数集合:

-   \\(\mathcal{IF} \subseteq \mathcal{BF}\\)；
-   \\(\mathcal{BF}\\) 对于复合封闭，即对于任意的 \\(m, n \in \mathbb{N}^+\\)，\\(f : \mathbb{N}^m \rightarrow \mathbb{N}\\)，\\(g\_1, g\_2, \dots, g\_m : \mathbb{N}^n \rightarrow \mathbb{N}\\)，若 \\(f, g\_1, g\_2, \dots, g\_m \in \mathcal{BF}\\)，则 \\(\operatorname{\mathrm{Comp}}[f, g\_1, g\_2, \dots, g\_m] \in \mathcal{BF}\\)。

</div>

即 \\(\mathcal{BF}\\) 是 \\(\mathcal{IF}\\) 在函数复合下的闭包：

<div class="fact">

\\(\mathcal{BF} = \\\{ A : \mathcal{IF} \subseteq A \land \text{$A$ is closed under composition}\\\}\\).

</div>

<div class="theorem">

设 \\(f\\) 为数论函数，\\(f \in \mathcal{BF}\\) 下当且仅当存在数论函数序列 \\(f\_0, f\_1, \dots, f\_n\\)，使得 \\(f = f\_n\\)，且对于 \\(0 \leq i \leq n\\)，\\(f\_i\\) 满足下述条件之一:

-   \\(f\_i \in \mathcal{IF}\\)；或
-   存在 \\(k, m > 0\\) 及 \\(i\_0, i\_1, \dots, i\_k < i\\) 之间（允许某个 \\(i\_u = i\_v\\)），使得 \\(f\_{i0} : \mathbb{N}^m \rightarrow \mathbb{N}\\)，\\(f\_{i\_1}, \dots, f\_{i\_k} : \mathbb{N}^m \rightarrow \mathbb{N}\\)

    \\[f\_i = \operatorname{\mathrm{Comp}}^m\_k[f\_{i\_0}, f\_{i\_1}, \dots, f\_{i\_k}]\\]

    即由其前 \\(k+1\\) 个函数 \\(f\_{i\_0}, f\_{i\_1}, \dots, f\_{i\_k}\\) 复合而来。

函数序列 \\(f\_0, f\_1, \dots, f\_n\\) 被称为基本函数 \\(f\\) 的构造过程。注意，\\(f\\) 的构造过程可能不唯一。

设 \\(f\\) 的最短构造过程为 \\(f\_0, f\_1, \dots, f\_n\\)，则 \\(n\\) 被称为 \\(f\\) 的构造长度。

</div>

<div class="proof">

设

\\[ \mathcal{BF} = \\\{ f : f \text{ is constructed with } f\_0, \ldots, f\_n \\\}. \\]

欲证 \\( \mathcal{BF}' = \mathcal{BF} \\)，只需证 \\( \mathcal{BF} \subseteq \mathcal{BF}' \\) 且 \\( \mathcal{BF}' \subseteq \mathcal{BF} \\)。

易见 \\( \mathcal{IF} \subseteq \mathcal{BF}' \\) 且 \\( \mathcal{BF}' \\) 对于复合封闭，因此 \\( \mathcal{BF} \subseteq \mathcal{BF}' \\)。

设 \\( A \\) 为一个满足 \\( \mathcal{IF} \subseteq A \\) 且对于复合封闭的集合，下面证 \\( \mathcal{BF}' \subseteq A \\)：

设 \\( f \in \mathcal{BF} \\)，对 \\( f \\) 的构造长度 \\( l \\) 作归纳证明 \\( f \in A \\):

-   当 \\(l = 0 \\) 时，由 \\( f \in \mathcal{IF} \\)，故 \\( f \in A \\)。
-   设 \\( \forall l \le n. f\_l \in A \\)。当 \\( l = n + 1 \\) 时，设 \\( f \\) 的最短构造过程为 \\( f\_0, \dots, f\_{n}, f\_{n+1} \\)，则有两种情况：
    -   若 \\( f\_{n+1} \in \mathcal{IF} \\)，则 \\( f = f\_{n+1} \in A \\)；
    -   若 \\( f\_{n+1} \\) 由其前 \\( k+1 \\) 函数 \\( f\_{l\_0}, f\_{l\_1}, \dots, f\_{l\_k} \\) 复合而得。其中 \\(f\_{l\_0} : \mathbb{N}^k \rightarrow \mathbb{N}\\) 且 \\(f\_{n\_1}, \dots, f\_{n\_k} : \mathbb{N}^m \rightarrow \mathbb{N}\\)。

        \\(\forall 0 \le i \le l. f\_i\\) 存在构造过程 \\(f\_0, f\_1, \dots, f\_i\\)，其构造长度 \\(l\_i \le i \le l\\)，根据归纳假设，\\(\forall 0 \le i \le l. f\_i \in A\\)。由于 \\(A\\) 对于复合封闭，故

\\[ f\_{n + 1} = \operatorname{\mathrm{Comp}}^{m}\_{k} [f\_{l\_0}, f\_{l\_1}, \dots, f\_{l\_k}] \in A \\]

综上所述，若 \\( f \in \mathcal{BF}' \\)，则 \\( f \in A \\)，因此 \\( \mathcal{BF}' \subseteq A \\)。由 \\(A\\) 的任意性知 \\( \mathcal{BF}' \subseteq \mathcal{BF} \\)。

故 \\( \mathcal{BF} = \mathcal{BF}' \\)。

</div>

根据上述定理，要证明 \\(f \in \mathcal{BF}\\)，只需作出 \\(f\\) 的构造过程。

<div class="theorem">

对任意 \\( k \in \mathbb{N}^+ \\), \\( f : \mathbb{N}^k \rightarrow \mathbb{N} \\), 若 \\( f \in \mathcal{BF} \\), 存在常数 \\( h \\), 使得：

\\[ f(\vec{x}) < \\| \vec{x} \\| + h. \\]

其中 \\( \\| \vec{x} \\| = \max \\\{ x\_{i} : 1 \leq i \leq k \\\} . \\)

</div>

<div class="proof">

对 \\(f\\) 的构造长度进行归纳。

由于 \\( f \in \mathcal{BF} \\)，故存在构造序列 \\( \\{f\_0, f\_1, \ldots, f\_l\\} \\) 使得 \\( f = f\_l \\)。

下面对 \\( l \\) 做数学归纳。

-   当 \\( l = 0 \\) 时，由 \\( f\_0 \in \mathcal{IF} \\)。若 \\( f\_0 \\) 为 \\( Z \\)，则 \\( Z(x) = 0 < \\|\vec{x}\\| + 2 \\)；若 \\( f\_0 \\) 为 \\( S \\)，则 \\( S(x) = x + 1 < \\|\vec{x}\\| + 2 \\)；若 \\( f\_0 \\) 为 \\( P^k\_i \\)，则 \\( P^k\_i(\vec{x}) < \\|\vec{x}\\| + 2 \\)。

-   假设对于所有 \\( 0 \leq i \leq k \\)，结论对 \\( f\_i \\) 成立。

    当 \\( k + 1 \\) 时，有 \\( f\_{k+1}(\vec{x}) = f\_{i\_0}(f\_{i\_1}(\vec{x}), \ldots, f\_{i\_t}(\vec{x})) < \max\\{f\_{i\_j}(\vec{x}) : 1 \leq j \leq t\\} + h\_0 < \max\\{\\|\vec{x}\\| + h\_j : 1 \leq j \leq t\\} + h\_0 = \\|\vec{x}\\| + h\_0 + \max\\{h\_j : 1 \leq j \leq t\\} \\)

    令 \\( h = h\_0 + \max\\{h\_j : 1 \leq j \leq t\\} \le 2 \max \\\{ h₀, hⱼ \\\} \\)，结论成立，并且可以发现 \\( h \le 2^{l + 1} \\)。

因此，存在 \\( h \\)，使得对于所有 \\( \vec{x} \\)，有 \\( f(\vec{x}) < \\|\vec{x}\\| + h \\)。

</div>

从这个定理中可以看出，\\( \mathcal{BF} \\) 中的函数的增长速度是有限的。

<div class="theorem">

假设 \\( f: \mathbb{N}^n \rightarrow \mathbb{N} \\)，其中 \\( n \in \mathbb{N}^+ \\)，\\( f \in BF \\)，则 \\( f(\vec{x}) \\) 仅与 \\( \vec{x} \\) 的某一分量有关，与其他分量无关。

</div>

<div class="proof">

由于 \\( f \in \mathcal{BF} \\)，存在构造序列 \\( f\_0, f\_1, \ldots, f\_n \\) 使得 \\( f = f\_n \\)。

现在对 \\( n \\) 进行数学归纳。

-   当 \\( n = 0 \\) 时，由 \\( f\_0 \in \mathcal{IF} \\)
    -   如果 \\( f\_0 \\) 是 \\( Z \\) 或 \\( S \\)，那么结论成立。
    -   如果 \\( f\_0 \\) 是 \\( P^i\_n \\)，则 \\( P^i\_n(\vec{x}) = x\_i \\)，仅与 \\( \vec{x} \\) 的第 \\( i \\) 分量有关，因此结论成立。

-   假设当 \\( 0 \leq i \leq k \\) 时，对于 \\( f\_i \\) 结论成立。

    当 \\( k + 1 \\) 时，\\( f\_{k+1}(\vec{x}) = f\_{i\_0}(f\_{i\_1}(\vec{x}), \ldots, f\_{i\_m}(\vec{x})) \\)。由归纳假设，\\( f\_{i\_0}(\vec{x}) \\) 仅与 \\( \vec{x} \\) 的某一分量有关，不妨设为第 \\( j \\) 分量。再由 \\( f\_j(\vec{x}) \\) 仅与 \\( \vec{x} \\) 的某一分量有关，不妨设为第 \\( t \\) 分量。因此，\\( f\_{k+1}(\vec{x}) \\) 仅与 \\( \vec{x} \\) 的第 \\( t \\) 分量有关。

综上所述，结论成立。

</div>

从这个定理中可以看出，\\( \mathcal{BF} \\) 中的函数的值仅与其参数的某一分量有关。因此可以得到一个有趣的性质：多元函数 \\( f(\vec{x}) \\) 可以简化成一元函数 \\( f(x\_i) \\)，并且如果函数的构造过程中出现了 \\(P^n\_m\\)，那么它一定出现在开头。

根据上面两个定理，可以证明 \\(f(x, y) = x + y\\) 和 \\( f(x, y) = x \dot - y \\)  不属于 \\( \mathcal{BF} \\)。

根据第二个定理不难发现，多元函数 \\( f(\vec{x}) \\) 可以简化成一元函数 \\( f(x\_i) \\)，那么 \\( P^n\_m \\) 将不再有用处。此时可以证明 \\( f \\) 一定是一元函数。

<div class="theorem">

设函数 \\( f(\vec{x}) \in \mathcal{BF} \\)，则 \\( f(\vec{x}) \\) 一定是常函数或线性函数（仅与 \\( \vec{x} \\) 的某一分量相关）。

</div>

<div class="proof">

由上一个定理，这里将 \\( \vec{x} \\) 简化成 \\( x \\)。

对 \\( f \\) 的构造长度进行归纳。

-   当 \\( l = 0 \\) 时

    -   若 \\( f\_0 \\) 为 \\( Z \\)，则 \\( Z(x) = 0 \\) 为常函数
    -   若 \\( f\_0 \\) 为 \\( S \\)，则 \\( S(x) = x + 1 \\) 为线性函数
    -   若 \\( f\_0 \\) 为 \\( P^1\_1 \\)，则 \\( P^1\_1(x) = x \\) 为线性函数

    均成立

-   假设对于所有 \\( 0 \leq i \leq k \\)，\\( f\_i \\) 都是线性函数。

    当 \\( k + 1 \\) 时，

    \\[
        f\_{k+1}(x) = f\_{i\_0}(f\_{i\_1}(x), \ldots, f\_{i\_m}(x)) = f\_{i\_0}(f\_{i\_j}(x)) = \begin{cases}
            c, & f\_{i\_0}(x) = c, \\\\
            c + h\_0, & f\_{i\_0}(x) = x + h\_0 \wedge f\_{i\_j}(x) = c, \\\\
            x + h\_0 + h\_j, & f\_{i\_0}(x) = x + h\_0 \wedge f\_{i\_j}(x) = x + h\_j.
        \end{cases}
      \\]

    仍然是线性函数。

综上所述，结论成立。

</div>


## 配对函数 {#配对函数}

<div class="definition">

**(配对函数)**

设 \\( \operatorname{pg}(x,y) : \mathbb{N}^2 \rightarrow \mathbb{N} \\), \\( K(x) : \mathbb{N} \rightarrow \mathbb{N} \\), \\( L(x) : \mathbb{N} \rightarrow \mathbb{N} \\) 为数论函数，若它们对于任意 \\( x, y \in \mathbb{N} \\)，满足

\\[ K(\operatorname{pg}(x,y)) = x, \\]

\\[ L(\operatorname{pg}(x, y)) = y, \\]

则称 \\( \operatorname{pg} \\) 为配对函数（pairing function），\\( K \\) 和 \\( L \\) 分别为左函数和右函数，\\( \\{ \operatorname{pg}, K, L \\} \\) 为配对函数组。

</div>

<div class="definition">

**(Gödel 编码)**

设 \\( n \in \mathbb{N} \\)，令 \\( g : \mathbb{N}^{n+1} \rightarrow \mathbb{N} \\) 定义为

\\[ g(x\_0, \dots, x\_n) = \prod\_{i=0}^{n} p\_{i}^{x\_{i}} \\]

其中 \\( p\_i \\) 表示第 \\( i \\) 个素数。

\\( g(x\_{0}, \dots, x\_{n}) \\) 记作 \\( \langle x\_{0}, \dots, x\_{n} \rangle \\)，称为 \\( x\_{0}, \dots, x\_{n} \\) 的 **Gödel 编码**。

</div>

<div class="definition">

**(多元配对函数)**

设 \\( n \in \mathbb{N} \\)，若函数 \\( J\_n : \mathbb{N}^{n+1} \rightarrow \mathbb{N} \\)，且 \\( \pi\_0, \dots, \pi\_n : \mathbb{N} \rightarrow \mathbb{N} \\)。

\\[\forall i \le n. \forall x\_0, \ldots, x\_n \in \mathbb{N}. \pi\_i(J\_n(x\_0, \ldots, x\_n)) = x\_i \\]

则称 \\( J\_n \\) 为多元配对函数，\\( \\\{ J\_n, \pi\_0, \ldots, \pi\_n \\\} \\) 为多元配对函数组。通常将 \\( J\_n(x\_0, \ldots, x\_n) \\) 简记为 \\( [x\_0, \ldots, x\_n] \\)，将 \\( \pi\_i(z) \\) 简记为 \\( (z)\_i \\)。

</div>

<div class="definition">

**(Gödel \\( \beta \\)-函数)** 对任何 \\( x, i \in \mathbb{N} \\)，令

\\[ \beta(x, i) = \text{rs}(K(x), 1 + (i + 1)L(x)), \\]

其中
\\[ K(x) = x - \lfloor \sqrt{x} \rfloor^2, \\]
\\[ L(x) = K(\lfloor \sqrt{x} \rfloor), \\]

\\( \text{rs}(x, y) \\) 为求余函数。

</div>

<div class="theorem">

对任何自然数的有限序列 \\( y\_0, \ldots, y\_{n-1} \in \mathbb{N} \\)，存在 \\( x \in \mathbb{N} \\) 使得对所有 \\( i < n \\)，有 \\( \beta(x, i) = y\_i \\)。

</div>

<div class="proof">

设 \\( y\_0, \ldots, y\_{n-1} \in \mathbb{N} \\)，令 \\( S = \max\\{y\_0, \ldots, y\_{n-1}, n\\} \\)。对于每个 \\( i < n \\)，令
\\[ m\_i = 1 + (i + 1) \times S!, \\]
其中 \\( S! \\) 表示 \\( S \\) 的阶乘。

首先我们将证明，对于任意的 \\( i < j < n \\)，有 \\( \gcd(m\_i, m\_j) = 1 \\)。反设存在素数 \\( p \\) 满足 \\( p | m\_i \\) 且 \\( p | m\_j \\)，则 \\( p | (m\_j - m\_i) \\)。而 \\( m\_j - m\_i = (j - i) \times S! \\)，从而 \\( p | (j - i) \times S! \\)。因为 \\( p | m\_i \\)，即 \\( p | (1 + (i + 1) \times S!) \\)，从而 \\( p \nmid S! \\)。但因为 \\( j - i < S \\)，故 \\( p | (j - i) \times S! \\) 产生矛盾。

因此对于任意的 \\( i < j < n \\)，\\( \gcd(m\_i, m\_j) = 1 \\) 成立。对于同余方程组
\\[ y\_i \equiv v \pmod{m\_i}, \quad i = 0, 1, \ldots, n-1, \\]

由中国剩余定理知其有解，设解为 \\( v \\)。取 \\( x = \operatorname{J}(v, S!) \\)，其中 \\( \operatorname{J}(x, y) \\) 为前文定义的配对函数，则若 \\( i < n \\)，则
\\[ K(x) = v, \\]
\\[ L(x) = S!. \\]
\\[ \beta(x, i) = \text{rs}(K(x), 1 + (i + 1)L(x)) \\]
\\[ = \text{rs}(v, 1 + (i + 1) \times S!) \\]
\\[ = \text{rs}(v, m\_i) = y\_i. \\]

</div>


## 初等函数 {#初等函数}

<div class="definition">

初等函数（elementary function）类 \\( \mathcal{EF} \\) 是满足以下条件的最小集：

1.  \\( \mathcal{IF} \subseteq \mathcal{EF} \\)；
2.  \\( X+Y \\), \\( X \ddot{-} Y \\), \\( X \times Y \\), \\( \lfloor X/Y \rfloor \\) 属于 \\( \mathcal{EF} \\)；
3.  \\( \mathcal{EF} \\) 对于复合、有界递加算子 \\( \Sigma[\cdot] \\) 和有界递乘算子 \\( \Pi[\cdot] \\) 封闭。

</div>

<div class="theorem">

在 \\( \mathcal{EF} \\) 的定义中，函数 \\( x+y \\), \\( x \times y \\), \\( \lfloor x/y \rfloor \\) 可省。

</div>

<div class="proof">

\\[x \times y = \sum\_{i=0}^{x} [y] \ddot{-} y \Rightarrow g(x, y) = \sum\_{i=1}^{x}[P\_2^2(i, y)], \times = \operatorname{\mathrm{Comp}}\_2^2[\ddot{-}, g, P\_2^2]\\]

---

\\[x + y = S(x) \times S(y) \ddot{-} S(x \times y) \Rightarrow + = \operatorname{\mathrm{Comp}}\_2^2[\ddot{-}, \operatorname{\mathrm{Comp}}\_2^2[\times, S \circ P\_1^2, S \circ P\_2^2], S \circ \times]\\]

---

比较复杂的是除法。

首先定义 \\(N\\) 和 \\(N^2\\)：

\\[N(x) = \prod\_{i=0}^x [i \ddot{-} 1] \Rightarrow g = \operatorname{\mathrm{Comp}}\_2^1[\ddot{-}, P\_1^1, S \circ Z], N(x) = \prod\_{i=0}^x[g(i)]\\]

\\[N^2(x) = N(N(x)) \Rightarrow N^2 = N \circ N\\]

---

然后可以定义 \\(\dot{-}\\)：注意到 \\(x \dot{-} y = (x \ddot{-} y) \times N^2(((y \ddot{-} x) + x) \ddot{-} y)\\)，则令

\\[g(x, y) = (((y \ddot{-} x) + x) \ddot{-} y = \operatorname{\mathrm{Comp}}\_2^2[\ddot{-}, \operatorname{\mathrm{Comp}}\_2^2[+, \operatorname{\mathrm{Comp}}\_2^2[\ddot{-}, P\_2^2, P\_1^2], P\_1^2], P\_2^2]\\]

因此：

\\[\dot{-} = \operatorname{\mathrm{Comp}}\_2^2[\times, \ddot{-}, N^2 \circ g]\\]

---

注意到 \\(\lfloor x / y \rfloor = N^2(y \times \sum\_{i=0}^x[N(y \times (i+1) \dot{-} x)])\\)，则令

\\[g\_0(i, x, y) = N(y \times (i + 1) \dot{-} x) = \operatorname{\mathrm{Comp}}\_1^3[N, \operatorname{\mathrm{Comp}}\_2^3[\ddot{-}, \operatorname{\mathrm{Comp}}\_2^3[\times, P\_3^3, \operatorname{\mathrm{Comp}}\_1^3[S, P\_1^3]], P\_2^3]]\\]

\\[g\_1(n, x, y) = \sum\_{i=0}^n[g\_0(i, x, y)] = \sum\_{i=0}^x[N(y \times (i + 1) \dot{-} x)]\\]

\\[g\_2(x, y) = g\_1(x, x, y) = \sum\_{i=0}^x[N(y \times (i + 1) \dot{-} x)] = \operatorname{\mathrm{Comp}}\_3^2[g\_1, P\_1^2, P\_1^2, P\_2^2]\\]

\\[g\_3(x, y) = N^2(y) = \operatorname{\mathrm{Comp}}\_1^2[N^2, P\_2^2]\\]

因此

\\[\lfloor / \rfloor = \operatorname{\mathrm{Comp}}\_2^2[\times, g\_3, g\_2]\\]

</div>

<div class="theorem">

设 \\( f \\) 为数论函数，\\( f \in \mathcal{EF} \\) 当且仅当存在数论函数序列 \\( f\_0, \ldots, f\_n \\)，使得 \\( f = f\_n \\)，且对于 \\( 0 \leq i \leq n \\)，\\( f\_i \\) 满足以下条件之一：

-   \\( f\_i \\) 属于原始函数集合 \\( \mathcal{P} \\) 或 \\( \\{ f : f(x, y) = x \ddot{-} y \\} \\)；

-   存在 \\( k, m > 0 \\) 及 \\( i\_0, \ldots, i\_k < i \\)（允许某个 \\( i\_u = i\_v \\)），使得 \\( f\_i: \mathbb{N}^k \rightarrow \mathbb{N} \\)，\\( f\_{i\_0}, \ldots, f\_{i\_k}: \mathbb{N}^m \rightarrow \mathbb{N} \\)，且

    \\[ f\_i = \operatorname{\mathrm{Comp}}\_k^m[f\_{i\_0}, f\_{i\_1}, \ldots, f\_{i\_k}] \\]

-   存在 \\( j < i \\) 及 \\( m \in \mathbb{N} \\)，使得 \\( f\_i: \mathbb{N}^{m+1} \rightarrow \mathbb{N} \\) 且

    \\[ f\_i(t, \vec{x}) = \sum\_{k=0}^{t} [f\_j(k, \vec{x})] \\]

-   存在 \\( j < i \\) 及 \\( m \in \mathbb{N} \\)，使得 \\( f\_i: \mathbb{N}^{m+1} \rightarrow \mathbb{N} \\) 且

    \\[ f\_i(t, \vec{x}) = \prod\_{k=0}^{t} [f\_j(k, \vec{x})] \\]

函数序列 \\( f\_0, \ldots, f\_n \\) 被称为初等函数 \\( f \\) 的构造过程。设 \\( f \\) 的最短构造过程为 \\( f\_0, \ldots, f\_n \\)，则 \\( n \\) 被称为 \\( f \\) 的构造长度。

</div>

<div class="theorem">

\\( \mathcal{EF} \\) 对于有界 \\( \mu \\)-算子是封闭的。

</div>

<div class="proof">

下面用闭区间 \\([0,n]\\) 表示集合 \\(\\{0,1,2,\ldots,n\\}\\)。

易见

\\[
\sum\_{i=0}^{n} [N^2(f(i, vec{y}))] = \begin{cases}
0, & \exists x \in [0, y]. f(x, y) = 0, \\\\
n+1, & \text{else}
\end{cases}
\\]

因此

\\[
\left[\sum\_{i=0}^{n}[\prod\_{j=0}^i \left[N^2(f(j, \vec{y})) \right] \right] = \begin{cases}
\mu x \leq n.[f(x, \vec{y})], & \exists x \in [0, n]. f(x, \vec{y}) = 0 \\\\
0, & \text{else}
\end{cases}
\\]

从而

\\[
\mu x \leq n. [f(x,\vec{y})] = \left[\sum\_{i=0}^{n}[\prod\_{j=0}^i \left[N^2(f(j, \vec{y})) \right] \right] \ddot{-} \sum\_{i=0}^{n} [N^2(f(i, \vec{y}))]
\\]

若 \\( f \in \mathcal{EF} \\)，则由上式知 \\( g(n) = \mu x \leq n.[f(x,y)] \in \mathcal{EF} \\)。故 \\( \mathcal{EF} \\) 对有界 \\( \mu \\)-算子封闭。

</div>

<div class="definition">

**(数论谓词的特征函数)**

设 \\( p \\) 为 \\( n \\) 元数论谓词，其特征函数 \\( \chi: \mathbb{N}^n \rightarrow \\{ 0, 1 \\} \\)，定义如下：

\\[
\chi(\vec{x}) = \begin{cases}
0, & p(\vec{x}), \\\\
1, & \neg p(\vec{x})
\end{cases}
\\]

</div>

<div class="definition">

**(初等数论谓词)**

若 \\( n \\) 元数论谓词 \\( p \\) 的特征函数 \\( \chi\_p \in \mathcal{EF} \\)，则称 \\( p \\) 是初等的。

</div>

比较数论谓词都是初等数论谓词。
