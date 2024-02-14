+++
title = "[TaPL] 06 Nameless Representation of Terms"
author = ["roife"]
date = 2021-04-24
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论", "程序语义", "Lambda演算", "de Bruijn"]
draft = false
+++

## Variable Representations {#variable-representations}

1.  Represent variables symbolically, with variable renaming mechanism to avoid capture
2.  Represent variables symbolically, with bound variables and free variables are all different (**Barendregt convention**)
3.  Some "canonical" representation of variables and terms that does not require renaming
4.  Avoid substitution by mechanisms such as **explicit substitutions**
5.  Avoid variables (**Combinatory Logic**)

下面讲的是第三种，可以避免 alpha-conversion。


## Terms and Contexts {#terms-and-contexts}

De Bruijn 的做法是用自然数来表示变量，其中当前层对应的 bound variables 的编号为 \\(0\\)；使用外层 bound variables 时，从内到外的 binder 依次加一。

这样的项被称为 **De Bruijn terms**，变量被称为 **De Bruijn indices**。例如：

\begin{aligned}
    \mathtt{fix} &= \lambda f. (\lambda x. f\ (\lambda y. x\ x\ y))\ (\lambda x. f\ (\lambda y. x\ x\ y))\\\\
    &= \lambda.(\lambda. 1\ (\lambda. (1\ 1)\ 0))(\lambda. 1\ (\lambda. (1\ 1)\ 0)); \\\\
    \mathtt{f} &= (\lambda x. x\ y\ (\lambda y. y\ x\ z)) \\\\
    &= (\lambda. 0\ 1\ (\lambda. 0\ 1\ 2));
\end{aligned}

下面定义了 De Bruijn terms。在 de Bruijn 表示方法下，abstraction 就写作 \\(\lambda. t\\) 而非 \\(\lambda x. t\\)。

<div class="definition">

**(Terms)**

Let \\(\mathcal{T}\\) be the smallest family of sets \\(\\{\mathcal{T}\_0, \mathcal{T}\_1, \mathcal{T}\_2, \dots\\}\\) such that

1.  \\(k \in \mathcal{T}\_n\\) whenever \\(0 \le k < n\\)
2.  if \\(t\_1 \in \mathcal{T}\_n\\) and \\(n > 0\\), then \\(\lambda. t\_1 \in \mathcal{T}\_{n-1}\\)
3.  if \\(t\_1 \in \mathcal{T}\_n\\) and \\(t\_2 \in \mathcal{T}\_n\\), then \\((t\_1\ t\_2) \in \mathcal{T}\_n\\)

</div>

其中，\\(T\_n\\) 集合中的项被称为 **\\(n\\)-terms**，其中的项包含了不超过 \\(n\\) 个自由变量，编号为 \\(0 \dots n-1\\)。当 \\(t \in T\_0\\)，\\(t\\) 是一个封闭项。

在 \\(\lambda . t\\) 中的 term \\(t\\) 里，\\(0\\) 就恰好代表当前这层的 binder，其他的 indices 都可以看作 free variables。


### Naming context {#naming-context}

对于包含自由变量的 terms，其中的自由变量需要用到 naming context。

<div class="definition">

**(Naming context)**

Suppose \\(x\_0 \dots x\_n\\) are variable names from \\(\mathcal{V}\\) . The **naming context** \\(\Gamma = x\_n, x\_{n−1}, \dots, x\_1, x\_0\\) assigns to each \\(x\_i\\) the de Bruijn index \\(i\\).

Note that the rightmost variable in the sequence is given the index \\(0\\); this matches the way we count λ binders --- from right to left --- when converting a named term to nameless form. We write \\(dom(Γ)\\) for the set \\(\\{x\_n, \dots ,x\_0\\}\\) of variable names mentioned in \\(\Gamma\\).

</div>

对于自由变量，用一个 naming context \\(\Gamma\\) 记录变量和其对应的编号。两个不同的变量（包括 binder 和自由变量）对应的编号应当不同。Naming context 中所有的变量直接线性排列为 \\(x\_n, \dots, x\_0\\)，且 \\(x\_i \mapsto i\\)。其中当前层所对应的 binder 恰好为 \\(x\_0\\)，对应 \\(0\\)。

<div class="sample">

对于 context \\(\Gamma = x \rightarrow 4; y \rightarrow 3; z \rightarrow 2; a \rightarrow 1; b \rightarrow 0\\)，

\\(\lambda w. y\ w\\) 可以表示成 \\(\lambda . 4\ 0\\)。在 \\(w\\) 这层的 naming context 为 \\(x : 5, y : 4, z : 3, a : 2, b : 1, w : 0\\)。其中 \\(x, y, z, a, b\\) 均为自由变量。

如果现在处于从外到内第 \\(i\ (i \ge 0)\\) 层的 abstraction，且自由变量 \\(x\\) 对应的编号为 \\(j\ (j \ge 0)\\)，则 \\(x\\) 对应的编号为 \\(j + i + 1\\)。

</div>


## Shifting and Substitution {#shifting-and-substitution}

为了实现 substitution，需要一个叫 shifting 的操作来改变**自由变量**的编码。例如下面的式子进行替换时，\\(s\\) 的 λ 的深度多了一层，因此自由变量的编码都要增加 \\(1\\)。

\begin{aligned}
     {}& [x \mapsto s\]\(\lambda y. x) \quad \text{where $s = z\ (\lambda w.w)$} \\\\
    ={}& \lambda y. z\ (\lambda w.w)
\end{aligned}

Shifting 函数 \\(\uparrow^d\_c\\) 包括两个参数：

-   \\(d\\) 表示自由变量编号的变化量
-   \\(c\\) 是 cutoff 参数，用来识别自由变量。该参数以 \\(0\\) 为起点，并且每次遇到一个 binder 就加一。对于 \\(\uparrow^d\_c(t)\\) 内部有 \\(c\\) 个 binders，则 \\(0 \dots c-1\\) 是 bound variables，\\(k \ge c\\) 则是需要被 shift 的自由变量。

<div class="definition">

**(Shifting)**

The **\\(d\\)-place shift** of a term \\(t\\) above cutoff \\(c\\), written \\(\uparrow^d\_c (t)\\), is defined as follows:

\begin{alignat\*}{2}
&\uparrow^d\_c(k) &&=
    \begin{cases}
        k & \text{if $k < c$} \\\\
        k+d & \text{if $k \ge c$}
    \end{cases}\\\\
&\uparrow^d\_c(\lambda. t\_1) &&= \lambda. \uparrow^d\_{c+1} (t\_1) \\\\
&\uparrow^d\_c(\lambda. t\_1\ t\_2) &&={} \uparrow^d\_c(\lambda. t\_1)\ \uparrow^d\_c(\lambda. t\_2)
\end{alignat\*}

\\(\uparrow^d\_0 (t)\\) 可以记作 \\(\uparrow^d (t)\\)

</div>

> if \\(t\\) is an \\(n\\)-term, then \\(\uparrow^d\_c (t)\\) is an \\((n+d)\\)-term.

进行替换的时候，如果是 \\([0 \mapsto s]t\\)，显然直接将 \\(0\\) 替换成 \\(s\\) 即可，否则每遇到一个 binder，意味着进入了下一层 abstraction，所以对应的数字要减一。

<div class="definition">

**(Substitution)**

The substitution of a term \\(s\\) for variable number \\(j\\) in a term \\(t\\), written \\([j \mapsto s]t\\), is defined as follows:

\begin{aligned}
&[j \mapsto s]k &&=
  \begin{cases}
      s & \text{if $k = j$} \\\\
      k & \text{otherwise}
  \end{cases}\\\\
&[j \mapsto s\]\(\lambda. t\_1) &&= \lambda. [j+1 \mapsto \uparrow^1 (s)] (t) \\\\
&[j \mapsto s\]\(t\_1\ t\_2) &&= ([j \mapsto s]t\_1\ [j \mapsto s]t\_2)
\end{aligned}

</div>

<div class="sample">

令 \\(\Gamma = \\{b:0, a:1\\}\\)

\begin{aligned}
    [b \mapsto a\ (\lambda z. a)]\ (b\ (\lambda x. b)) &= [0 \mapsto 1\ (\lambda. 2)]\ (0\ (\lambda. 1)) \\\\
    &= (1\ (\lambda. 2))\ (\lambda. (2\ (\lambda. 3))) \\\\
    &= (a\ (\lambda z. a))\ (\lambda x. (a\ (\lambda z.a)))
\end{aligned}

</div>

> if \\(s\\) and \\(t\\) are \\(n\\)-terms and \\(j \le n\\), then \\([j \mapsto s]t\\) is an \\(n\\)-term.


## Evaluation {#evaluation}

进行 evaluation 时会消耗 bound variables，此时必须对变量进行重新编号：

\\[
(\lambda. 1\ 0\ 2)\ (\lambda. 0) \rightarrow 0\ (\lambda. 0)\ 1 \qquad \text{not $1\ (\lambda.0)\ 2$}
\\]

对于 \\(\lambda. t\\)，进行 evaluation 后，\\(t\\) 中的自由变量的编号需要减一。因此，需要一个函数 \\(\uparrow^{-1}\\) 来进行逆操作。然而替换进去的 \\(v\\) 并没有消耗掉任何 bound variables，因此不需要重新编号，可以提前进行 \\(\uparrow^{1}\\) 来抵消掉 \\(\uparrow^{-1}\\)。

对应的需要改变 beta-conversion 的规则：

\\[
(\lambda. t\_{12})\ v\_2 \rightarrow \uparrow^{-1}([0 \mapsto \uparrow^1(v\_2)]t\_{12}) \tag{E-AppAbs}
\\]

其它规则和原来相同。


## de Bruijn levels {#de-bruijn-levels}

**de Bruijn levels** 是一种和 de Bruijn indices 同构的表示方法，与 indices 的差别在于后者是从内到外编码，而前者是从外到内编码，例如：\\(\lambda x. (\lambda y. x\ y)\ x = \lambda. (\lambda. 0\ 1)\ 0\\)。
