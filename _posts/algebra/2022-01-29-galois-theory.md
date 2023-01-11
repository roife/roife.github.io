---
layout: "post"
title: "Galois 理论"
subtitle: "Galois 基本定理与方程可解性"
author: "roife"
date: 2022-01-29

tags: ["代数@数学", "数学@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 扩域

如果域 $E$ 包含域 $F$，则称 $E$ 是 $F$ 的**扩域**，记作 $F \subseteq E$或者 $E / F$。

扩域的例子：
- 实数域 $\mathbb{R}$ 就是有理数域 $\mathbb{Q}$ 的扩域
- $a + b \sqrt{2}$ 组成的域 $\mathbb{Q}[\sqrt{2}]$ 是 $Q$ 的扩域

如果 $F$ 是一个域，$\alpha \in F$ ，但是 $\sqrt{α} \ne F$ ，则 $F_1 = F [\sqrt{α}]$ 仍是一个域。类似可以定义

$$
F_2 = F_1[\sqrt{\beta}] = F[\sqrt{\alpha}][\sqrt{\beta}] = F[\sqrt{\alpha}, \sqrt{\beta}]
$$

由此可以得到一个扩域系列：$\mathbb{Q} \subset F_1 \subset F_2 \dots F_n$。

包含方程 $p(x) = 0$ **全部根**的**最小扩域**叫做 $p(x)$ 的**分裂域**，也称为**根域**。

例如方程 $x^2 - 2 = 0$ 的根域是 $\mathbb{Q}[\sqrt{2}]$。对于多项式方程，如果能从基本域有理数域开始，通过一系列上述扩域，最终到达根域，那么此方程是可以用根式解的。

类似可以推广到高次根式：对域 $F$ 逐一地用根式进行扩域，从而得到 $F[\alpha_1][\alpha_2] \cdots [\alpha_k]$。如果每次扩张所用的 $\alpha_i$ 都是根式（即 $\alpha_i^k \in F[\alpha_1, \dots, \alpha_{i-1}]$），则称扩域 $F[\alpha_1, \alpha_2, \dots,\alpha_k]$  为 $F$ 的**根式扩域**。设方程的根是 $x_1, x_2, \dots, x_n$，其分裂域 $E = Q[x_1, x_2, \dots, x_n]$ 是根式扩域，则称方程是**根式可解**的。

域 $F$ 上的扩张 $K$ 可以看做 $F$ 上的一个线性空间，$K$ 对 $F$ 的维数称为扩张 $K/F$ 的**次数**，记作 $[K:F]$。如果 $[K:F]$ 为一有限数，则称 $K/F$ 为**有限扩张**，否则称为**无限扩张**。$K$ 对$F$ 的一个基也称为扩张 $K/F$ 的**基**。例如扩张 $\mathbb{Q}[\sqrt{2}, \sqrt{3}] / \mathbb{Q}$ 的基为 $\\{1, \sqrt{2}, \sqrt{3}, \sqrt{6}\\}$，$[\mathbb{Q}[\sqrt{2}, \sqrt{3}] : \mathbb{Q}] = 4$。

# 对称多项式

$$
\sigma_i = \sum \prod_{\vert r_{k_j} r_{k_{j+1}} \dots r_{k_i}\vert = i} r_{k_j} r_{k_{j+1}} \dots r_{k_i}
$$

例如 $\sigma_3 = r_1 r_2 r_3 + r_1 r_2 r_4 + \dots r_{n-2} r_{n-1} r_n$。

牛顿定理：任何关于 $r_1, r_2, \dots, r_n$ 的对称多项式都可用基本对称多项式 $\sigma_1, \sigma_2, \dots,\sigma_n$ 来表示。

例如 $(r_1 - r_2)^2 = \sigma_1^2 - 4 \sigma_2^2$。

# 自同构

域的**自同构**是一个**可逆函数** $f : F \rightarrow F$。它将域一一映射到自身，并满足：
- $f(x + y) = f(x) + f(y)$
- $f(ax) = f(a)f(x)$（易得 $f(x)^a = f(x^a)$）
- $f \left (\frac{1}{x} \right ) = \frac{1}{f(x)}$

可以定义 $\mathbb{Q}[\sqrt{2}]$ 上的自同构：$f(a + b \sqrt{2}) = a - b \sqrt{2}$。

一个域的全体自同构的集合记作 $\mathrm{Aut}(F)$。自同构是一个函数，自同构间的二元运算即函数的复合变换，单位元即恒等变换。对任意 $\mathrm{Aut}(F)$ 中的两个自同构 $f, g$，定义二元运算 $(f \cdot g)(x) = f (g(x))$，则 $\mathrm{Aut}(F)$ 在这个运算下构成一个群，称为**自同构群**。

对于数域 $F$ 而言，有 $\mathbb{Q} \subset F$，因此 $\forall x \in \mathbb{Q}\ \forall \sigma \in \mathrm{Aut}(F), \sigma(x) = x$，且 $\mathrm{Aut}(\mathbb{Q}) = \{e\}$，其中 $e$ 为恒等变换。

如果 $E$ 是 $F$ 的扩域，并且域 $E$ 的自同构 $f$ 满足 $\forall x \in F, f (x) = x$，则称为 $E$ 上的 **$F$-自同构**，所有 $F$-自同构组成的群记作 $\mathrm{Aut}_F(E)$。

域的自同构说明我们可以重新调换域中的元素，而完全不影响域的结构。例如对于方程 $x^2 - 2 = 0$ 其解为 $x = \plusmn \sqrt{2}$，调换 $\sqrt{2}$ 与 $-\sqrt{2}$，结果不变。对于任何仅有 $\sqrt{2}$ 进行乘法与加法的方程（$a + b \sqrt{2}$），调换 $\plusmn \sqrt{2}$ 都不会影响解。

对于方程 $x^2 - 1 = 0$ 的分裂域 $\mathbb{Q}[\sqrt{2}]$，共有两个 $\mathbb{Q}$-自同构：
- $f(a + b \sqrt{2}) = a - b \sqrt{2}$
- $g(x) = x$

对于方程 $x^4 - 1 = 0$ 的分裂域 $\mathbb{Q}[i]$，共有两个 $\mathbb{Q}$-自同构：
- $f(a + b i) = a - b i$
- $g(x) = x$

对于每个 $Q[x_1, \dots, x_n]$ 的根式扩域 $E$，都存在一个更大的根式扩域 $E \subseteq \overline{E}$，使得所有 $x_1, \dots, x_n$ 的置换都有自同构 $\sigma$。

> 对于 $\mathbb{Q}$ 上的多项式 $p(x)$，若 $E/Q$ 是扩域，$f$ 是 $E$ 上的 $\mathbb{Q}$-自同构，则有 $f(p(x)) = p(f(x))$。
>
> **证明**：
>
> 令 $p(x) = \sum_{i=0}^n a_i x^i, a_i \in \mathbb{Q}$
>
> $$
> f(p(x)) = f(\sum_{i=0}^n a_i x^i) = \sum_{i=0}^n f(a_i) f(x^i) = \sum_{i=0}^n a_i f(x^i) = \sum_{i=0}^n a_i f(x)^i = p(f(x))
> $$

# 伽罗瓦群

可以看出自同构类似于置换群：对调某些元素，而保持其他元素不变。因此可以用类似置换群的方法来描述域的自同构。

对于 $F$ 的扩域 $E$，定义 $G$ 为 $E$ 的 $F$-自同构构成的集合，称 $G$ 为扩域 $E/F$ 的**伽罗瓦群**，记为 $\mathrm{Gal}(E/F)$。

例如对于 $\mathbb{Q}[\sqrt{2}]$，伽罗瓦群 $G = \mathrm{Gal}(\mathbb{Q}[\sqrt{2}]/\mathbb{Q}) = \\{f, g\\}$，其中 $f(a + b \sqrt{2}) = a - b \sqrt{2}$，$g(x) = x$。单位元为 $g$。可以验证 $f \cdot f = g$。这说明 $G \cong C_2$，可以表示为 $G = (f) = \\{f, f^2\\}$。同时 $G \cong S_2$，写成置换群的形式为 $\\{(1), (1\ 2)\\}$，其中 $(1\ 2)$ 表示对调两个根。

下面举一些伽罗瓦群的例子（构造伽罗瓦群时只考虑引起扩域的元素的映射满足性质即可）：
- 对于方程 $x^2 - bx + c = 0$ 来说，解为 $x_{1, 2} = \frac{b \plusmn \sqrt{b^2 - 4c}}{2}$，其伽罗瓦群有三种情况：
  - 有两个有理根 $x = \frac{b \plusmn r}{2}$，则 $G = \\{e\\}$，其中 $e(x) = x$ 为恒等变换。$G$ 是 $S_2$ 的一个子群
  - 有两个无理根 $x = \frac{b \plusmn \sqrt{d}}{2}$，则 $G = \\{e, \sigma\\}$，其中 $\sigma(p + q \sqrt{d}) = p - q \sqrt{d}, e(x) = x$。$\mathrm{Gal}(\mathbb{Q}[\sqrt{d}]/\mathbb{Q}) \cong S_2$
  - 有两个复数根 $x = \frac{b \plusmn i\sqrt{d}}{2}$，则 $G = \\{e, \sigma\\}$，其中 $\sigma(p + qi) = p - qi, e(x) = x$。$\mathrm{Gal}(\mathbb{Q}[i]/\mathbb{Q}) \cong S_2$
  - 其中，后面两种情况在分裂域上是同构的，均有 $G \cong S_2 \cong Z_2 \cong C_2$
- 对于方程 $(x^2-2)^3(x^2-3) = 0$，分裂域为 $\mathbb{Q}[\sqrt{2}, \sqrt{3}]$，其伽罗瓦群有四个元素：
  - 设 $\sigma \in \mathrm{Gal}(\mathbb{Q}[\sqrt{2}, \sqrt{3}]/\mathbb{Q}), \sigma(\sqrt{2}) = \plusmn \sqrt{2}, \sigma(\sqrt{3}) = \plusmn \sqrt{3}$，因此 $\sigma$ 有四种选择
  - $\mathrm{Gal}(\mathbb{Q}[\sqrt{2}, \sqrt{3}]/\mathbb{Q}) = \\{e, (1\ 2), (3\ 4), (1\ 2)(3\ 4)\\}$，为 $S_4$ 的子群
- 对于方程 $x^3 - 2 = 0$，分裂域为 $\mathbb{Q}[\sqrt[3]{2}, \omega]$
  - 方程有三个根 $\alpha_1 = \sqrt[3]{2}, \alpha_2 = \omega \sqrt[3]{2}, \alpha_3 = \omega^2 \sqrt[3]{2}$
  - $(\sigma(\omega))^3 = 1$，$(\sigma(\sqrt[3]{2}))^3 = 2$
  - 考虑 $\sqrt[3]{2} \xrightarrow{\sigma} \\{ \alpha_1, \alpha_2, \alpha_3 \\}$，$\omega \xrightarrow{\sigma} \\{ \omega, \omega^2 \\}$，共 $6$ 种情况
- 如果 $p$ 是素数，则方程 $x^p − 1$ 的伽罗瓦群是循环群 $C_{p−1}$
  - 方程的 $p$ 个解分别为 $1, \omega, \omega^2, \dots, \omega^{p-1}$ 是在复平面单位元上的 $p$ 个点，可以表示为 $e^{\frac{2 k \pi}{p} i}$。方程的分裂域为 $\mathbb{Q}[\omega]$
  - 考虑伽罗瓦群 $\mathrm{Gal}(\mathbb{Q}[\omega]/\mathbb{Q})$ 中的某个自同构 $h$，有 $\omega^p = 1 \Leftrightarrow h(\omega)^p = h(\omega^p) = 1$，即 $h(\omega)$ 是 $p$ 次单位根之一
    - 这里如果 $p$ 不是素数，则单位根的幂 $\zeta_m^k = e^{\frac{2 \pi m k i}{n}}$，当 $mk = n$ 时 $\zeta_m^k = 1$
  - 令 $h_i(\omega) = \omega^i\ (1 \le i \le p - 1)$（$i \ne 0$，因为 $h_i(1) = \omega^0 = 1$）
  - 构造一一映射 $\mathrm{Gal}(\mathbb{Q}[\omega]/\mathbb{Q}) \overset{\sigma}{\rightarrow} C_{p-1} : \sigma(h_i) = i$
  - 由于 $(h_i \cdot h_j)(\omega) = h_i(h_j(\omega)) = h_i(\omega^j) = \omega^{ij}$，因此 $\sigma(h_i \cdot h_j) = ij = \sigma(i) \cdot \sigma(j)$
  - 综上，有 $\mathrm{Gal}(\mathbb{Q}[\omega]/\mathbb{Q}) \cong C_{p-1}$。且循环群 $\mathrm{Gal}(\mathbb{Q}[\omega]/\mathbb{Q}) = (h_1)$
  - 事实上，方程 $x^n - 1 = 0$ 的伽罗瓦群与整数模 $n$ 乘法群 $Z^*_n$ 同构
- 对于方程 $x^4 + x^3 + x^2 + x + 1 = 0$，其分裂域为 $\mathbb{Q}[\zeta]$（$\zeta^5 = 1$）
  - 其四个根为 $\zeta, \zeta^2, \zeta^3, \zeta^4$
  - 设 $\sigma \in \mathrm{Gal}(\mathbb{Q}[\zeta]/\mathbb{Q})$，则 $(\sigma(\zeta))^5 = 1$ 又 $\sigma(\zeta) \ne 1$，则 $\sigma$ 有四种选择 $\zeta, \zeta^2, \zeta^3, \zeta^4$
  - 因此 $\mathrm{Gal}(\mathbb{Q}[\zeta]/\mathbb{Q}) = \\{e, (1\ 2\ 4\ 3), (1\ 3\ 4\ 2), (1\ 2)(3\ 4)\\}$，为 $S_4$ 的子群

多项式伽罗瓦群中的每个映射都对应着根的一组置换，即域 $F$ 上的 $n$ 次多项式 $f(x)$（即 $f(x)$ 的系数均在 $F$ 上）的伽罗瓦群同构于对称群 $S_n$ 的一个子群。

# 正规扩张

对于扩张 $E/F$，当$F[x]$ 中的不可约多项式在 $E$ 内有根时，此不可约多项式在 $E$ 内可以完全分解成一次因式的乘积，那么 $E/F$ 被称为**正规扩张**。有限扩张 $E/F$ 是正规扩张当且仅当 $E$ 是 $F[x]$ 中某一多项式的分裂域。

对于有限扩张 $K/F$，如果 $E/K$ 是正规扩张，且当中间域 $L\ (F \subset L \subset E)$ 包含 $K$ 且 $L/F$ 正规时必有 $L = E$（理解为 $E$ 是最小的正规扩张），则称 $E/F$ 为 $K/F$ 的一个**正规闭包**。

若 $E/F$ 为正规扩张，且 $\sigma \in \mathrm{Gal}(E/F)$，则 $\sigma$ 将 $F$ 上多项式 $f(x)$ 的根 $\alpha \in E$ 变为根 $\sigma(\alpha) \in E$。

例如对于方程 $x^3 - 2 = 0$，分裂域 $\mathbb{Q}[\sqrt[3]{2}, \omega]$ 是正规扩张，而 $\mathbb{Q}[\sqrt[3]{2}]$ 不是正规扩张。由于 $2$ 的三次根 $\omega \sqrt[3]{2}, \omega^2 \sqrt[3]{2}$ 均不在 $\mathbb{Q}[\sqrt[3]{2}]$ 中，所以 $\mathrm{Gal}(\mathbb{Q}[\sqrt[3]{2}]) = \\{ e \\}$。而 $\mathbb{Q}[\sqrt[3]{2}, \omega]$ 就是 $\mathbb{Q}[\sqrt[3]{2}]$ 的正规闭包。

# 伽罗瓦扩张

对于 $\mathrm{Aut}_F(E)$ 的子群 $H$，如果 $x \in E$ 满足 $\forall \sigma \in H, \sigma(x) = x$，则称 $x$ 为其**不动元**。全体不动元构成了 $H$ 的**不动域**，记作 $\mathrm{Inv}(H) = \\{ x \in E \vert \forall \sigma \in H, \sigma(x) = x \\}$。因为 $\forall x \in F \subset E\ \forall \sigma \in \mathrm{Gal}(E/F), \sigma(x) = x$，所以 $F \subseteq \mathrm{Inv}(\mathrm{Gal}(E/F))$。

例如令 $E = \mathbb{Q}[\sqrt[3]{2}], F = \mathbb{Q}$ 对于扩张 $E/F$，$\mathrm{Gal}(E/F) = \\{e\\}$。因此 $\mathrm{Inv}(\mathrm{Gal}(E/F)) = E$，这里扩张 $\mathrm{Inv}(\mathrm{Gal}(E/F))$ 比 $F$ 大。

如果 $F = \mathrm{Inv}(\mathrm{Gal}(E/F))$，则称 $E/F$ 为一个**伽罗瓦扩张**。伽罗瓦扩张是正规扩张。

伽罗瓦扩张有以下性质：
- 设 $E/F$ 为有限伽罗瓦扩张，则 $\mathrm{Gal}(K/F)$ 的阶等于 $[K:F]$
- 若域 $E$ 的一个有限自同构群 $G$ 以 $F$ 为不动域，则 $K/F$ 为有限伽罗瓦扩张且 $G = \mathrm{Gal}(E/F)$
- 若有限扩张 $E/F$ 有一自同构群 $G$ 满足 $\vert G \vert = [E:F]$，则 $E/F$ 为伽罗瓦扩张且 $G = \mathrm{Gal}(K/F)$

# 伽罗瓦基本定理

**伽罗瓦对应**：对于扩张 $E/F$，在 $\mathrm{Gal}(E/F)$ 的**子群集**和 $E/F$ 的**中间域集**之间存在一一映射：
- 每个子群 $H$ 对应于它的不动域 $H \rightarrow \mathrm{Inv}(H)$
- 每个中间域 $L$ 对应于 $E$ 对 $L$ 的伽罗瓦群 $L \rightarrow \mathrm{Gal}(E/L)$

**伽罗瓦基本定理**：对于伽罗瓦扩张 $E/F$，若 $F \subset L \subset E$，则存在 $\mathrm{Gal}(E/F)$ 的子群 $H$ 满足 $H = \mathrm{Gal}(E/L)$。

随着域不断扩张 $F \subset F_1 \subset F_2 \subset \dots \subset E$，对应的群不断减小。其中 $F \mapsto \mathrm{Gal}(E/F)$，$E \mapsto \\{e\\}$，中间域 $L \mapsto \mathrm{Gal}(E/L) \subset \mathrm{Gal}(E/F)$。因此扩域关系和子群关系是一对反序的关系。如果 $H = \mathrm{Gal}(E/L)$ 是正规子群，则其商群 $G/H = \mathrm{Gal}(L/F)$。

伽罗瓦对应有以下性质：
- $\mathrm{Gal}(E / \mathrm{Inv}(H)) = H$，$\mathrm{Inv}(\mathrm{Gal}(E / L)) = L$
- 若 $H_1 \subset H_2$，则 $\mathrm{Inv}(H_2) \subset \mathrm{Inv}(H_1)$
- $[E : \mathrm{Inv}(H)] = \vert H \vert$，$[\mathrm{Inv}(H):F] = [G:H]$

例如对于方程 $p(x) = x^4 − 8x^2 + 15 = 0$，$p(x) = (x^2 - 3)(x^2 - 5)$。其分裂域为 $E = \mathbb{Q}[\sqrt{2}, \sqrt{3}]$。伽罗瓦群 $\mathrm{Gal}(E/Q)$ 的阶为 $4$，且 $\mathrm{Gal}(E/Q) \cong C_4$，只有 $2$ 阶子群。此时可以找到 $3$ 个中间扩域 $\mathbb{Q}[\sqrt{3}], \mathbb{Q}[\sqrt{5}], \mathbb{Q}[\sqrt{15}]$，其对应的群的阶均为 $2$。

将分裂域 $E$ 上的元素表示为 $\alpha = a + b\sqrt{3} + c\sqrt{5} + d\sqrt{15} = a + b\sqrt{3} + c\sqrt{5} + d\sqrt{15}$。令 $f$ 表示调换 $\plusmn \sqrt{3}$，$g$ 表示调换 $\plusmn \sqrt{5}$。则有以下对应关系：

![Galois Correspondence](/img/in-post/post-unplugged/galois-correspondence.png){:height="400px" width="400px"}

直观理解：每一次扩域都会增加一个基变量，因此就丧失了在这个维度上的自由度，可以在这个维度上施加的变换也减少了。

对于方程 $f(x) = x^4 + x^3 + x^2 + x + 1$，其伽罗瓦群 $\mathrm{Gal}(\mathbb{Q}[\zeta]/\mathbb{Q}) = \\{e, (1\ 2\ 4\ 3), (1\ 3\ 4\ 2), (1\ 4)(2\ 3)\\}$。其中 $H = \\{ e, (1\ 4)(2\ 3) \\}$ 是它的一个子群。下面求其对应的中间域：
- 设 $\alpha \in \mathbb{Q}[\zeta]$，则 $\alpha = \alpha_0 + \alpha_1 \zeta + \alpha_2 \zeta^2 + \alpha_3 \zeta^3 + \alpha_4 \zeta^4$
- 由不动域定义有 $(1\ 4)(2\ 3) \alpha = \alpha$ 即 $\zeta$ 和 $\zeta^4$ 对调、$\zeta^2$ 和 $\zeta^3$ 对调，值不变
- 因此 $a_1 = a_4$，$a_2 = a_3$，即 $\alpha = \alpha_0 + \alpha_1 (\zeta + \zeta^4) + \alpha_2 (\zeta^2 + \zeta^3)$
- 又由 $\zeta^4 + \zeta^3 + \zeta^2 + \zeta + 1 = 0$，知 $\alpha = \alpha_0 + \alpha_1 (\zeta + \zeta^4) + \alpha_2 (-1 - (\zeta + \zeta^4))$
- 即 $\mathrm{Inv}(H) = \mathbb{Q}[\zeta + \zeta^4] = \mathbb{Q}[\zeta^2 + \zeta^3] = \mathbb{Q}(\sqrt{5})$

# 方程可解性

为了简化问题，首先增加一些额外的限制：
- 假设每次根式扩域 $F[\alpha_i]$ 中加入的 $\alpha_i$ 都是素数次方根
  - 例如对$\sqrt[6]{α}$ 分为 $\sqrt{α} = β$ 和 $\sqrt[3]{β}$，然后分两次进行根式扩域
- 如果 $\alpha_i$ 是 $p$ 次方根，且需要加入 $p$ 次单位根 $\zeta$，则先进行扩域 $F[\alpha_1, \alpha_2, \dots, \alpha_{i-1}, \zeta]$，再进行扩域 $F[\alpha_1, \alpha_2, \dots, \alpha_{i-1}, \zeta, \alpha_i]$

根式扩域 $F[\alpha_1, \dots, \alpha_n]$ 可以形成一个根式扩张链：

$$
F = F_0 \subseteq F_1 \subseteq \dots \subseteq F_k = F[\alpha_1, \dots, \alpha_n]
$$

其中每个 $F_i = F_{i−1}[\alpha_i]$，而 $\alpha_i$ 是 $F_{i−1}$ 中某个元素的素数次方根。与之对应的是一条子群链：

$$
\mathrm{Gal}(F_k/F_0) = G_0 \rhd G_1 \rhd \dots \rhd G_k = \mathrm{Gal}(F_k/F_k) = \{e\}
$$

其中 $G_i = \mathrm{Gal}(F_k/F_i) = \mathrm{Gal}(F_k/F_{i−1}[\alpha_i])$。每一步从 $G_{i−1}$ 前进到它的子群 $G_i$，都对应向域 $F$ 中扩张素数次方根 $\alpha_i$。即 $G_i$ 是前一个群 $G_{i-1}$ 的正规子群，且其商群 $G_{i-1}/G_i$ 是一个阿贝尔群。

> **定理** 如果扩域 $B \subseteq B[\alpha] \subseteq E$ 中，$\alpha^p \in B$，$p$ 是素数，并且满足上面的单位根的条件。则 $\mathrm{Gal}(E/B[\alpha])$ 是群 $\mathrm{Gal}(E/B)$ 的正规子群，且商群 $\mathrm{Gal}(E/B)/\mathrm{Gal}(E/B[\alpha])$ 是阿贝尔群。
>
> **证明**：
> 考虑利用群同态基本定理证明，因此需要找到 $\mathrm{Gal}(E/B)$ 上的同态满射，同态的核为 $\mathrm{Gal}(E/B[\alpha])$，且同态的目标是一个阿贝尔群（这样就能使得商群也是阿贝尔群）。
>
> 设同态为 $f$，核 $\mathrm{Gal}(E/B[\alpha])$ 中的变换都映射为恒等变换，即 $f$ 将 $E$ 中不在 $B[\alpha]$ 里的基都映射成了恒等变换（$B[\alpha]$ 中的基不受影响，因为本来就是恒等变换）（因此同态映射后对于 $E - B[\alpha]$ 的基的变换都消失了，剩下的变换都是对 $B[\alpha]$ 的变换）。
>
> 对于映射 $\sigma : E \rightarrow E \in \mathrm{Gal}(E/B)$，同态 $f$ 会将 $\sigma$ 从 $E$ 压缩到 $B[\alpha]$ 中，即 $f(\sigma) : B[\alpha] \rightarrow B[\alpha]$。记这个同态为 $\vert_{B[\alpha]}$，有
>
> $$ \tau \in \mathrm{Gal}(E/B[\alpha]) \Leftrightarrow \tau \vert_{B[\alpha]} = e \text{ is the identity map}$$
>
> 并且同态性 $\forall{\sigma, \sigma'} \in \mathrm{Gal}(E/B), (\sigma'\sigma) \vert_{B[\alpha]} = \sigma' \vert_{B[\alpha]} \circ \sigma \vert_{B[\alpha]}$ 成立。
>
> 设 $\sigma \in \mathrm{Gal}(E/B)$，根据伽罗瓦群的定义，$\sigma$ 是 $B$-自同构的映射，则 $\sigma$ 对 $B$ 中的元素是恒等映射，因此 $\sigma \vert_{B[\alpha]}$ 对 $B$ 中元素也是恒等映射（恒等映射同态后仍是恒等映射）。所以 $\sigma \vert_{B[\alpha]}$ 只和基 $\alpha$ 的映射 $\sigma(\alpha)$ 有关。下面有两种情况：
> - $\alpha = \zeta$。其中 $\zeta$ 是 $p$ 次单位根。此时 $(\sigma(\alpha))^p = \sigma(\alpha^p) = \sigma(\zeta^p) = \sigma(1) = 1$。因此 $\sigma(\alpha) = \zeta^i = \alpha^i \in B[\alpha]\ (1 \le i \le p-1)$
> - $\alpha \ne \zeta$，则 $\alpha^p \in B$。$(\sigma(\alpha))^p = \sigma(\alpha^p) = \alpha^p \in B$，因此 $\sigma(\alpha) = \zeta^j \alpha\ (1 \le j \le p - 1)$，其中 $\zeta \in B$ 且 $\zeta^p = 1$。因此 $\sigma(\alpha) \in B \subset B[\alpha]$
>
> 由上可知 $\sigma$ 在 $B[\alpha]$ 上封闭。同时可以发现 $\vert_{B[\alpha]}$ 将 $\mathrm{Gal}(E/B)$ 映射到 $\mathrm{Gal}(B[\alpha]/B)$。
>
> 下面证明 $\mathrm{Gal}(B[\alpha]/B)$ 是阿贝尔群：
> - $\alpha = \zeta$。那么 $\sigma \vert_{B[\alpha]} \in \mathrm{Gal}(B[\alpha]/B)$ 可以写成 $\sigma_i'(\alpha) = \alpha^i$ 的形式，因此
>   $$\sigma_i'\sigma_j'(\alpha) = \alpha^{ij} = \sigma_j'\sigma_i'(\alpha)$$
> - $\alpha \ne \zeta$。那么 $\sigma_i'(\alpha) = \zeta^i \alpha$，因此
>   $$\sigma_i'\sigma_j'(\alpha) = \zeta^{i+j}\alpha = \sigma_j'\sigma_i'(\alpha)$$
> 由于 $\zeta \in B$，因此 $\sigma \vert_{B[\alpha]}(\zeta) = \zeta$。
> 因此 $\mathrm{Gal}(B[\alpha]/B)$ 是阿贝尔群。
>
> **引申** 如果 $E/B$ 是伽罗瓦扩张，$E \supset K \supset B$ 且 $K/B$ 也是伽罗瓦扩张，则 $f : \mathrm{Gal}(E/B) \rightarrow \mathrm{Gal}(K/B)$ 是核为 $\mathrm{Gal}(E/K)$ 的同态满射

在伽罗瓦群的子群链中，如果每个群 $G_i$ 都是 $G_{i-1}$ 的正规子群，并且商群 $G_{i-1} / G_i$ 是阿贝尔群，则称伽罗瓦群 $\mathrm{Gal}(F[\alpha_1, \dots, \alpha_k]/F)$ 是**可解的**。

$$
\mathrm{Gal}(F_k/F_0) = G_0 \rhd G_1 \rhd \dots \rhd G_k = \mathrm{Gal}(F_k/F_k) = \{e\}
$$

对于一般的 $n$ 次方程 $x^n + a_1 x^{n-1} + \dots + a_n = 0$。**基本域**为 $\mathbb{Q}[a_1, \dots, a_n]$，其 $N$ 个根所在的根域为 $\mathbb{Q}[x_1, \dots, x_n]$。如果对基本域做根式扩域，无法包含根域，则称方程是无法用根式求解的。

> **定理**：当 $n \ge 5$ 时，$\mathbb{Q}[a_1, \dots, a_n]$ 的根式扩域不包含根域 $\mathbb{Q}[x_1, \dots, x_n]$
>
> **证明**：
> 下用反证法证明：
>
> 设 $\mathbb{Q}[a_1, \dots, a_n]$ 的某个根式扩域 $E$ 包含 $\mathbb{Q}[x_1, \dots, x_n]$。那么一定存在一个更大的根式扩域 $E' \supseteq E$，使伽罗瓦群 $G_0 = \mathrm{Gal}(E'/\mathbb{Q}[a_1, \dots, a_n])$ 包含所有根的置换的自同构。此时可以构造一个根式扩域的子群链：
>
> $$G_0 \rhd G_1 \rhd \dots \rhd G_k = \{ e \}$$
>
> 根据上面证明的定理，每个 $G_i$ 都是 $G_{i−1}$ 的正规子群，并且商群 $G_{i−1}/G_i$ 可交换。$G_{i−1}$ 与商群之间有核为正规子群 $G_i$ 的同态映射，$\tau \sigma G_i = \sigma \tau G_i \Rightarrow \tau \in G_{i-1}, \sigma^{-1} \tau^{-1} \sigma \tau G_i = G_i$，所以有
>
> $$\forall \sigma, \tau \in G_{i-1}, \sigma^{-1} \tau^{-1} \sigma \tau \in G_i$$
>
> 当 $n \ge 5$ 时，由于 $G_0$ 包含所有根的置换的自同构，则 $G_0 \cong S_n$，则必然包含 $3$ 循环置换 $(a\ b\ c)$（$a, b, c$ 为元素而非置换）。如果 $G_i$ 包含 $3$ 循环置换，有（$n \ge 5$，因此可以取 $a, b, c, d, e$ 的置换）
>
> $$(a\ b\ c) = (d\ a\ c)^{−1}(c\ e\ b)^{−1}(d\ a\ c)(c\ e\ b) \in G_{i+1}$$
>
> 则 $G_{i+1}$ 也包含 $3$ 循环置换。但是 $G_{k} = \\{e\\}$，矛盾，因此原命题不成立。即一般 5 次方程不能用根式解。

对于 $S_5$ 来说，其唯一正规子群为 $A^5$，$A_5$ 的唯一正规子群为 $\\{e\\}$（即 $A_5$ 是单群，事实上 $\forall n \ge 5, A_n$ 都是单群），而 $A^5/\\{e\\}$ 不是交换的，因此不可解：$S_5 \rhd A_5 \rhd \\{e\\}$。

而 $S_4$ 的正规子群为 $A_4$，$A_4$ 的正规子群为克莱因群 $\\{(1), (12)(34), (13)(24), (14)(23)\\}$，是可交换的：$S_4 \rhd A_4 \rhd K_4 \rhd C_2 \rhd \\{e\\}$，对应商群的阶分别是 $2, 3, 2, 2$，都是素数，因此都是阿贝尔群。

$S_3$ 的正规子群为 $A_3$，交错群 $A_3$ 同构于 $C_3$，所以也是可交换的：$S_3 \rhd C_3 \rhd \\{e\\}$，对应商群的阶分别是 $2, 3$，都是素数，因此都是阿贝尔群。
