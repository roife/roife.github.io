---
layout: "post"
title: "「TaPL」 06 Nameless Representation of Terms"
subtitle: "匿名表示"
author: "roife"
date: 2021-04-24

tags: ["Types and Programming Languages@读书笔记", "读书笔记@Tags", "类型系统@程序语言理论", "程序语言理论@Tags", "λ 演算@函数式编程", "函数式编程@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# Variable Representations

1. Represent variables symbolically, with variable renaming mechanism to avoid capture
2. Represent variables symbolically, with bound variables and free variables are all different (**Barendregt convention**)
3. Some “canonical” representation of variables and terms that does not require renaming
4. Avoid substitution by mechanisms such as **explicit substitutions**
5. Avoid variables (**Combinatory Logic**)

下面讲的是第三种，可以避免 alpha-conversion。

# Terms and Contexts

De Bruijn 的做法是用自然数来表示变量，其中最内层为 $0$，从内到外的 binder 依次加一（the
variable bound by the $k$'th enclosing λ.）。这样的项被称为 De Bruijn terms，变量被称为 De Bruijn indices。例如：

$$
\begin{aligned}
    \mathtt{fix} &= \lambda f. (\lambda x. f\ (\lambda y. x\ x\ y))\ (\lambda x. f\ (\lambda y. x\ x\ y))\\
    &= \lambda.(\lambda. 1\ (\lambda. (1\ 1)\ 0))(\lambda. 1\ (\lambda. (1\ 1)\ 0)); \\
    \mathtt{f} &= (\lambda x. x\ y\ (\lambda y. y\ x\ z)) \\
    &= (\lambda. 0\ 1\ (\lambda. 0\ 1\ 2));
\end{aligned}
$$

> **Definitions**: Terms
>
> Let $\mathcal{T}$ be the smallest family of sets $\{\mathcal{T}_0, \mathcal{T}_1, \mathcal{T}_2, \dots\}$ such that
> 1. $k \in \mathcal{T}_n$ whenever $0 \le k < n$
> 2. if $t\_1 \in \mathcal{T}\_n$ and $n > 0$, then $\lambda. t\_1 \in \mathcal{T}\_{n-1}$
> 3. if $t\_1 \in \mathcal{T}\_n$ and $t_2 \in \mathcal{T}\_n$, then $(t\_1, t\_2) \in \mathcal{T}_{n-1}$

其中，$T_n$ 集合中的项被称为 **$n$-terms**，即包含了不超过 $n$ 个自由变量，编号为 $0 \dots n-1$。

对于 closed terms，那么显然它属于所有的 $\mathcal{T}_n$，而且其 de Bruijn representation 是唯一的。

## Naming context

对于包含自由变量的 terms，其中的自由变量需要用到 naming context。

> **Definition**
>
> Suppose $x_0$ through $x_n$ are variable names from $\mathcal{V}$ . The naming context $\Gamma = x_n, x_{n−1}, \dots, x_1, x_0$ assigns to each $x_i$ the de Bruijn index $i$. Note that the rightmost variable in the sequence is given the index $0$; this matches the way we count λ binders — from right to left — when converting a named term to nameless form. We write $dom(Γ)$ for the set $\{x_n, \dots ,x_0\}$ of variable names mentioned in $\Gamma$.

例如对于 naming context $\Gamma = x \rightarrow 4; y \rightarrow 3; z \rightarrow 2; a \rightarrow 1; b \rightarrow 0$，$\lambda w. \lambda y. w$ 可以表示成 $\lambda . \lambda . 4\ 0$。

即假设目前的深度为 $m$（当前层对应的 bound variable 为 $m$），那么自由变量即为 $m$ 加上 naming context 中的值 $x$：$m+x$。

# Shifting and Substitution

为了实现 substitution，需要一个叫 shifting 的操作来改变自由变量的编码。例如下面的式子进行替换时，$s$ 的 λ 的深度多了一层，因此自由变量的编码都要增加 $1$。

$$
\begin{aligned}
     {}& [x \mapsto s](\lambda y. x) \quad \text{where $s = z\ (\lambda w.w)$} \\
    ={}& \lambda y. z\ (\lambda w.w)
\end{aligned}
$$

Shifting 函数会用一个 cutoff 参数来控制哪个变量需要被 shift。该参数以 $0$ 为起点，并且每次遇到一个 binder 就加一。对于 $\uparrow^d_c(t)$ 内部有 $c$ 个 binders，则 $0 \dots c-1$ 是 bound variables，$k \ge c$ 则是需要被 shift 的自由变量。

> **Definition**: Shifting
>
> The $d$-place shift of a term $t$ above cutoff $c$, written $\uparrow^d_c (t)$, is defined as follows:
>
> $$
> \begin{alignat*}{2}
> &\uparrow^d_c(k) &&=
>     \begin{cases}
>         k & \text{if $k < c$} \\
>         k+d & \text{if $k \ge c$}
>     \end{cases}\\
> &\uparrow^d_c(\lambda. t_1) &&= \lambda. \uparrow^d_{c+1} (t_1) \\
> &\uparrow^d_c(\lambda. t_1\ t_2) &&={} \uparrow^d_c(\lambda. t_1)\ \uparrow^d_c(\lambda. t_2)
> \end{alignat*}
> $$
>
> $\uparrow^d_0 (t)$ 可以记作 $\uparrow^d (t)$

>  if $t$ is an $n$-term, then $\uparrow^d_c (t)$ is an $(n+d)$-term.

进行替换的时候，如果是 $[0 \mapsto s]t$，显然直接将 $0$ 替换成 $s$ 即可，否则每遇到一个 binder，意味着进入了下一层 abstraction，所以对应的数字要减一。

> **Definition**: Substitution
>
> The substitution of a term $s$ for variable number $j$ in a term $t$, written $[j \mapsto s]t$, is defined as follows:
>
> $$
> \begin{aligned}
> &[j \mapsto s]t &&=
>   \begin{cases}
>       s & \text{if $k = j$} \\
>       k & \text{otherwise}
>   \end{cases}\\
> &[j \mapsto s](\lambda. t_1) &&= \lambda. [j+1 \mapsto \uparrow^1 (s)] (t) \\
> &[j \mapsto s](\lambda t_1\ t_2) &&= ([j \mapsto s]t_1\ [j \mapsto s]t_2)
> \end{aligned}
> $$

$$
\begin{aligned}
    [b \mapsto a\ (\lambda z. a)]\ (b\ (\lambda x. b)) &= [0 \mapsto 1\ (\lambda. 2)]\ (0\ (\lambda. 1)) \\
    &= (1\ (\lambda. 2))\ (\lambda. (2\ (\lambda. 3))) \\
    &= (a\ (\lambda z. a))\ (\lambda x. (a\ (\lambda z.a)))
\end{aligned}
$$

> if $s$ and $t$ are $n$-terms and $j \le n$, then $[j \mapsto s]t$ is an $n$-term.


# Evaluation

进行 evaluation 时会消耗 bound variables，此时必须对变量进行重新编号：

$$
(\lambda. 1\ 0\ 2)\ (\lambda. 0) \rightarrow 0\ (\lambda. 0)\ 1 \qquad \text{not $1\ (\lambda.0)\ 2$}
$$

对应的需要改变 beta-conversion 的规则：

$$
(\lambda. t_{12})\ v_2 \rightarrow \uparrow^{-1}([0 \mapsto \uparrow^1(v_2)]t_{12}) \tag{E-AppAbs}
$$

其它规则和原来相同。

**de Bruijn levels** 是一种和 de Bruijn indices 同构的表示方法，与 indices 的差别在于后者是从内到外编码，而前者是从外到内编码，例如：$\lambda x. (\lambda y. x\ y)\ x = \lambda. (\lambda. 1\ 0)\ 0$。