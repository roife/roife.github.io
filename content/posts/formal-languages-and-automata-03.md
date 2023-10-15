+++
title = "[形式语言] 03 Regular Expression and Regular Language"
author = ["roife"]
date = 2023-09-23
series = ["formal-language-and-automata"]
tags = ["形式语言"]
draft = false
+++

## 正则表达式 {#正则表达式}


### 定义 {#定义}

<div class="definition">

**(正则表达式)**

设 \\(\Sigma\\) 是一个字母表，定义其上的**正则表达式**（Regular Expression, RE）如下构建：

-   \\(\emptyset\\) 是 \\(\Sigma\\) 上的正则表达式，表示语言 \\(\emptyset\\)
-   \\(\varepsilon\\) 是 \\(\Sigma\\) 上的正则表达式，表示语言 \\(\\{\varepsilon\\}\\)
-   \\(\forall a \in \Sigma\\) 是 \\(\Sigma\\) 上的正则表达式，表示语言 \\(\\{a\\}\\)
-   如果 \\(r, s\\) 是 \\(\Sigma\\) 上表达 \\(R\\) 和 \\(S\\) 的正则表达式，则
    -   \\(r + s\\) 是 \\(\Sigma\\) 上的正则表达式，表示语言 \\(R \cup S\\)
    -   \\(rs\\) 是 \\(\Sigma\\) 上的正则表达式，表示语言 \\(RS\\)
    -   \\(r\*\\) 是 \\(\Sigma\\) 上的正则表达式，表示语言 \\(R^\*\\)

</div>

<div class="definition">

**(正则表达式的等价)**

如果对于 \\(\Sigma\\) 上的正则表达式 \\(r, s\\)，有 \\(L( r) = L(s)\\)，则 \\(r = s\\)。

</div>

关于正则表达式一条很有趣的性质是 \\(L((r^\*s^\*)^\*) = L((r+s)^\*)\\)


### RE 与 FA 等价 {#re-与-fa-等价}

<div class="theorem">

正则表达式与有穷自动机等价。

</div>

<div class="proof">

为了证明这个问题，只需要证明对于任意正则表达式，存在一个 \\(\varepsilon\\)-NFA 与之等价；且对于任意 DFA，存在一个正则表达式与之等价。

-   对于任意正则表达式，存在一个 \\(\varepsilon\\)-NFA 与之等价

    只要根据正则表达式的构建树，按照下面的规则进行转换即可。

    {{< figure src="/img/in-post/post-formal-language-and-automata/re-to-fa-a.png" caption="<span class=\"figure-number\">Figure 1: </span>convert symbol from RE to FA" width="30%" >}}

    {{< figure src="/img/in-post/post-formal-language-and-automata/re-to-fa-eps.png" caption="<span class=\"figure-number\">Figure 2: </span>convert empty string from RE to FA" width="30%" >}}

    {{< figure src="/img/in-post/post-formal-language-and-automata/re-to-fa-empty.png" caption="<span class=\"figure-number\">Figure 3: </span>convert empty set from RE to FA" width="30%" >}}

    {{< figure src="/img/in-post/post-formal-language-and-automata/re-to-fa-concat.png" caption="<span class=\"figure-number\">Figure 4: </span>convert union from RE to FA" width="70%" >}}

    {{< figure src="/img/in-post/post-formal-language-and-automata/re-to-fa-union.png" caption="<span class=\"figure-number\">Figure 5: </span>convert concatenation from RE to FA" width="60%" >}}

    {{< figure src="/img/in-post/post-formal-language-and-automata/re-to-fa-star.png" caption="<span class=\"figure-number\">Figure 6: </span>convert kleene star from RE to FA" width="70%" >}}

-   对于任意 DFA 存在一个正则表达式与之等价

    首先对 DFA \\(M = (Q, \Sigma, \delta, q\_0, F)\\) 上的结点进行标号：\\(1, 2, \dots, n\\)。

    定义一条 \\(k\\)-路径为 DFA 上的一条路径，其中路径上的点（不包括起点和终点）的标号**不超过** \\(k\\)。因此所有路径都是 \\(n\\)-路径。路径上的边构成了一个句子。

    记 \\(R^k\_{ij}\\) 为点 \\(i\\) 到点 \\(j\\) 的所有 \\(k\\)-路径组成的语言，下面开始构造 \\(R^k\_{ij}\\)。

    -   当 \\(k=0\\) 时
        -   如果 \\(i = j\\)，则 \\(R^0\_{ii} = \varepsilon + a\_1 + a\_2 + \dots + a\_n (\delta(i, a\_l) = i) \\)
        -   如果 \\(i \ne j\\)，且不存在从 \\(i\\) 到 \\(j\\) 的路径，则 \\(R^0\_{ij} = \emptyset\\)
        -   如果 \\(i \ne j\\)，且存在从 \\(i\\) 到 \\(j\\) 的路径，则 \\(R^0\_{ij} = a\_1 + a\_2 + \dots + a\_n (\delta(i, a\_l) = j)\\)
    -   当 \\(k > 0\\) 时，假设所有 \\(k-1\\)-路径都可以转换成正则表达式

        -   则从 \\(i\\) 到 \\(j\\) 的路径有两种选择：不经过 \\(k\\) 或至少经过 \\(k\\) 一次
        -   因此 \\(R^k\_{ij} = R^{k-1}\_{ij} + R^{k-1}\_{ik} (R^k\_{kk})^{\*} R^{k-1}\_{kj}\\)

        根据这个方法可以构造出 \\(R^n\_{q\_0 q\_f} (q\_f \in F)\\)，此时 \\(R^n\_{q\_0q\_{f1}} + R^n\_{q\_0q\_{f2}} + \dots + R^n\_{q\_0q\_{fm}} (f\_i \in F)\\) 即是答案。

</div>


## 正则语言的性质 {#正则语言的性质}


### 泵引理 {#泵引理}

<div class="theorem">

**(Pumping Lemma)**

设 RL \\(L\\) 对应的 FA 为 \\(M\\)，则存在一个仅依赖于 \\(L\\) 的正整数 \\(N\\)。如果存在 \\(z \in L\\) 使得 \\(|z| \ge n\\)，那么 \\(\forall z \in L\\)，存在 \\(u, v, w\\) 使得：

-   \\(z = uvw\\)
-   \\(|uv| \le N\\)
-   \\(|v| \ge 1\\)
-   \\(\forall i \ge 0. u v^i w \in L\\)
-   \\(N < |M|\\)

</div>

<div class="proof">

设 RL \\(L\\)，DFA \\(M = (Q, \Sigma, \delta, q\_0, F)\\) 满足 \\(L(M) = L, |Q| = N\\)。为方便起见，不妨设 \\(M\\) 中不含不可达状态。

取 \\(z = a\_1 a\_2 \dots a\_m \in L (m \ge N)\\)，记 \\(z\\) 在 \\(M\\) 上经过的状态为 \\(q\_h = \delta(q\_0, a\_1 a\_2 \dots a\_h) (1 \le h \le m)\\)。

由于 \\(m \ge N\\)，因此存在 \\(q\_i, q\_j \in Q (1 < i < j < m = N)\\) 使得 \\(q\_i = q\_j\\)。即

\\[\delta(q\_0, a\_1 a\_2 \dots a\_i) = q\_i\\]
\\[\delta(q\_0, a\_1 a\_2 \dots a\_j) = q\_j = q\_i\\]

因此 \\(\forall k \ge 0, \delta(q\_i, (a\_{i+1} a\_{i+2} \dots a\_j)^k = q\_j = q\_i)\\)

因此，

\\[\forall k \ge 0, \delta(q\_0, a\_1 a\_2 \dots a\_i (a\_{i+1} a\_{i+2} \dots a\_j)^k a\_{j + 1} \dots a\_m) = a\_m\\]

取 \\(u = a\_1 a\_2 \dots a\_i, v = a\_{i+1} a\_{i+2} \dots a\_j, w = a\_{j+1} a\_{j+2} \dots a\_m \\)

则 \\(\forall i \ge 0\\) 有

-   \\(|uv| \le N\\)
-   \\(|v| \ge 1\\)

</div>

{{< figure src="/img/in-post/post-formal-language-and-automata/pumping-lemma.png" caption="<span class=\"figure-number\">Figure 7: </span>Pumping lemma" width="50%" >}}

泵引理是 RL 的必要条件，因此只能用来证明某些语言\*不是\*RL。为了简化证明，一般会构造一个 \\(uv\\) 为同一字符串重复的情况。

<div class="proposition">

证明 \\(L = \\{0^n | \text{$n$ is a prime number}\\}\\) 不是 RL。

</div>

<div class="proof">

设 \\(L\\) 是 RL，则 \\(L\\) 满足 pumping lemma。

设 \\(n\\) 是仅依赖于 \\(L\\) 的正整数，取 \\(z = 0^{n + p} \in L\\)，其中 \\(n + p\\) 是素数。由 pumping lemma 知存在 \\(z = uvw\\) 满足条件。由于 \\(|v| \ge 1\\)，不妨设 \\(v = 0^k\\)，\\(u = 0^{n - k}\\)。且 \\(\forall i \ge 0, uv^iw = 0^{n - k + ik + p} = 0^{n + p + (i - 1)k}\\)。

当 \\(i = n + p + 1\\) 时，\\(uv^iw = 0^{(n + p)(k + 1)}\\) 非素数，矛盾，因此原命题不成立。

</div>


### Myhill-Nerode 定理 {#myhill-nerode-定理}


#### Myhill-Nerode 定理及其证明 {#myhill-nerode-定理及其证明}

<div class="definition">

设 DFA \\(M = (Q, \Sigma, \delta, q\_0, F)\\)，\\(M\\) 在 \\(\Sigma^\*\\) 上的关系 \\(R\_M\\) 定义为

\\[\forall x, y \in \Sigma^\*, x R\_M y \Leftrightarrow \delta(q\_0, x) = \delta(q\_0, y)\\]

并定义

\\[ \mathrm{set}(q) = \\{ x | x \in \Sigma^\* \wedge \delta(q\_0, x) = q \\} \\]

即 \\( \forall x, y \in \Sigma^\*, x R\_M y \Leftrightarrow \exists q \in Q, x \in \mathrm{set}(q) \wedge y \in \mathrm{set}(q) \\)

</div>

<div class="definition">

设 \\(L \subseteq \Sigma^\*\\)，\\(L\\) 在 \\(\Sigma^\*\\) 上的关系 \\(R\_L\\) 定义为

\\[x R\_L y \Leftrightarrow (\forall z \in \Sigma^\*, xz \in L \Leftrightarrow yz \in L) \\]

</div>

这两个关系分别是在自动机和语言上的等价关系。

<div class="definition">

设 \\(R\\) 是 \\(\Sigma^\*\\) 上的等价关系，如果 \\(\forall x, y \in \Sigma^\*. xRy \rightarrow (\forall z. xzRyz)\\)，则称 \\(R\\) 是**右不变关系**（right invariant）等价关系。

</div>

根据上面的定义，不难得出 \\(R\_M\\) 和 \\(R\_L\\) 是右不变的等价关系。

<div class="definition">

设 \\(R\\) 是 \\(\Sigma^\*\\) 上的等价关系，\\(\Sigma^\*/R\\) 的一个元素是 \\(\Sigma^\*\\) 关于 \\(R\\) 的一个等价类，称 \\(|\Sigma^\* / R|\\) 称为 \\(R\\) 关于 \\(\Sigma^\*\\) 的**指数**（index）。

</div>

从定义中不难看出 \\(x R\_M y \Rightarrow x R\_{L(M)} y\\)，反之则未必成立。对于 DFA \\(M = (Q, \Sigma, \delta, q\_0, F)\\)，有

\\[|\Sigma^\* / R\_{L(M)}| \le |\Sigma^\* / R\_M| \le |Q| \\]

也就是说按照在自动机分出的等价类（自动机的状态数量），数量大于等于在语言分出的等价类（真实的等价类）。\\(R\_M\\) 的分类比 \\(R\_{L(M)}\\) 的更细，称 \\(R\_M\\) 是 \\(R\_{L(M)}\\) 的**加细**（refinement）。

<div class="theorem">

**(Myhill-Nerode)**

下面的三个命题等价：

-   \\(L \subseteq \Sigma^\*\\) 是 RL
-   \\(L\\) 是 \\(\Sigma^\*\\) 上的一个有穷指数、右不变、等价关系 \\(R\\) 的某些等价类的并
-   \\(R\_L\\) 具有有穷指数

</div>

<div class="proof">

下面通过证明 \\((1) \rightarrow (2) \rightarrow (3) \rightarrow(1)\\) 来证明。

-   \\((1) \rightarrow (2)\\)

    设 \\(L \subseteq \Sigma^\*\\) 是 RL，则存在 DFA \\(M(Q, \Sigma, \delta, q\_0, F)\\) 使得 \\(L(M) = L\\)。令关系 \\(R = R\_M\\)。

    -   由前面的定义知 \\(R\_M\\) 是 \\(\Sigma^\*\\) 上的右不变等价关系
    -   由 \\(|\Sigma^\* / R\_M| \le |Q|\\)，所以 \\(R\_M\\) 具有有穷指数
    -   如果 \\(x \in L\\)，那么 \\(\delta(q\_0, x) = t \in F\\)。因此 \\(\forall x \in L, x \in \mathrm{set}(t) (t \in F)\\)，所以 \\(L = \cup\_{t \in F}(\mathrm{set}(t))\\) 即 \\(L\\) 是 \\(R\\) 的某些等价类的并

-   \\((2) \rightarrow (3)\\)，因此需要证明 \\(R\\) 是 \\(R\_L\\) 的加细，即需要证明 \\( \forall x, y \in \Sigma^\*. x R y \rightarrow x R\_L y \\)

    由于 \\(R\\) 是右不变的，所以 \\(\forall z \in \Sigma^\*. xz R yz\\)。

    又由于 \\(L\\) 是 \\(R\\) 的部分等价类的并，因此 \\(xz \in L \Leftrightarrow yz \in L\\)。

    所以 \\(x R\_L y\\)。

-   \\((3) \rightarrow (1)\\)
    设 \\(R\_L\\) 具有有穷指数，下证存在 DFA \\(M\\) 使得 \\(L(M) = L\\)。

    令 \\(M = (\Sigma^\* / R\_L, \Sigma, \delta, [\varepsilon], \\{[x] | x \in L\\})\\)，其中 \\([x]\\) 表示 \\(x\\) 所在的等价类。

    其中对于任意的 \\(([x], a) \in (\Sigma^\* / R\_L) \times \Sigma\\)，有

    \\[\delta([x], a) = [xa]\\]

    下面证明 \\(\delta\\) 的相容性（是一个函数），即 \\(\forall [x], [y] \in (\Sigma\*/R\_L). [x] = [y] \rightarrow (\forall a \in \Sigma. \delta([x], a) = \delta([y], a))\\)。

    由于 \\([x] = [y]\\)，则 \\(x R\_L y\\)，又由于 \\(R\_L\\) 具有右不变形，所以 \\(\forall a \in \Sigma. [xa] = [ya]\\)，成立。因此 \\(M\\) 是一个合法的 DFA。

    根据 \\(R\_L\\) 的定义，\\(\forall x \in L. \delta(q\_0, x) \in \\{[x] | x \in L\\}\\)。

</div>


#### Myhill-Nerode 定理的推论 {#myhill-nerode-定理的推论}

<div class="theorem">

对任意 RL \\(L\\)，在同构意义下，接受 \\(L\\) 的最小 DFA 是唯一的。

</div>

<div class="proof">

设 \\(L\\) 是 RL，其最小 DFA \\(M = (Q, \Sigma, \delta, q\_0, F)\\) 满足 \\(L(M) = L\\)，显然 \\(M\\) 中不含不可达状态。根据前面的证明，有

\\[|\Sigma^\* / R\_M| \ge |\Sigma^\* / R\_L|\\]

下证 \\(M\\) 与 Myhill-Nerode 定理证明中的 \\(M' = (\Sigma^\* / R\_L, \Sigma, \delta', [\varepsilon], \\{[x] | x \in L\\})\\) 同构，其中

\\[\delta'([x], a) = [xa]\\]

定义映射 \\(f : Q \rightarrow \Sigma^\* / R\_L\\)，那么 \\(\forall q \in Q. \exists x \in \Sigma^\*. \delta(q\_0, x) = q\_x\\)。令

\\[f(q\_x) = f(\delta(q\_0, x)) = f(\delta'([\epsilon], x)) = [x]\\]

这样就建立起来从 \\(M\\) 到 \\(M'\\) 的映射。现在证明 \\(f\\) 是同构映射。

-   首先证明这是合法的函数，即 \\(q\_x = q\_y \Rightarrow \delta'([\varepsilon], x) = \delta'([\varepsilon], y)\\)
    -   \\(q\_x = q\_y \Leftrightarrow \delta(q\_0, x) = \delta(q\_0, y) \Leftrightarrow x R\_M y \Rightarrow x R\_L y \Leftrightarrow [{x}] = [y] \Leftrightarrow \delta'([\varepsilon], x) = \delta'([\varepsilon], y)\\)
-   证明单射，即 \\(q\_x \ne q\_y \Rightarrow \delta'([\varepsilon], x) \ne \delta'([\varepsilon], y)\\)
    -   \\(q\_x \ne q\_y \Leftrightarrow \delta(q\_0, x) \ne \delta(q\_0, y)\\)，即 \\(x\\) 和 \\(y\\) 在 \\(\Sigma^\*/R\_M\\) 的不同等价类中
    -   如果此时 \\([{x}] = [y]\\)，那么 \\(|\Sigma^\* / R\_M| > |\Sigma^\* / R\_L|\\)，这与 \\(M\\) 是最小 DFA 矛盾
    -   因此 \\([{x}] \ne [y]\\)，即 \\(\delta'([\varepsilon], x) \ne \delta'([\varepsilon], y)\\)
-   证明满射，即 \\(\forall [{x}]. \exists q\_x \in Q. f(q\_x) = [{x}]\\)
    -   \\(\forall x \in L. [{x}] = \delta'([\varepsilon], x) \Leftrightarrow \exists x \in L. \delta(q\_0, x) = q\_x\\)
-   证明同态映射。在自动机中，两个状态 \\(q \rightarrow p\\) 表示为 \\(\delta(q, a) = p\\)，因此即需要证明 \\(\delta(f(q), a) = f(p)\\)
    -   设 \\(\delta(q\_0, x) = q\\)
    -   \\(f(p) = f(\delta(q, a)) = f(\delta(\delta(q\_0, x), a)) = f(\delta(q\_0, xa)) = [xa]\\)，成立

综上，最小 DFA 都与唯一的 DFA 同构。

</div>


#### DFA 最小化 {#dfa-最小化}

根据 Myhill-Nerod 定理的推论，可以知道最小 DFA 是唯一的，并且其每个状态都对应了原来的语言中的一个等价类。因此只要合并原来的 DFA 中所有的等价类即可。

在具体计算时，状态 \\(\delta'([a\_1 a\_2 \dots a\_n], x) = \delta(a\_1, x) \vee \delta(a\_2, x) \vee \dots \vee \delta(a\_n, x)\\)。


### 判定性质 {#判定性质}

<div class="definition">

**(Decision Property)**

一类语言的**判定性质**（decision property）对应于一个算法，这个算法以某个语言的形式化描述为输入，然后判断这个语言是否满足某些性质。

</div>

下面将介绍一系列判定性问题，并给出对应的算法。


#### Membership Problem {#membership-problem}

<div class="question">

给定字符串 \\(w\\)，判定其是否属于某个正则语言 \\(L\\)？

</div>

<div class="answer">

模拟语言在 \\(L\\) 对应的的 DFA 上是否接受即可。

</div>


#### Emptiness Problem {#emptiness-problem}

<div class="question">

给定一个正则语言 \\(L\\)，问该语言是否为空？

</div>

<div class="answer">

构建该语言对应的 DFA，判定终点是否可达即可。

</div>

<div class="theorem">

设 DFA \\(M = (Q, \Sigma, \delta, q\_0, F)\\)，\\(L = L(M)\\) 是否为空的充要条件为

\\[\exists x \in \Sigma^{\*}. |x| < |Q| \wedge \delta(q\_0, x) \in F\\]

</div>


#### Infiniteness Problem {#infiniteness-problem}

<div class="question">

给定一个正则语言 \\(L\\)，问该语言是否无穷（该语言是否可以描述无穷的字符串）？

</div>

<div class="answer">

构建该语言的 DFA

1.  删除所有起点不可达状态
2.  删除所有不可达终点的状态
3.  判断图上是否有环

</div>

<div class="theorem">

设 DFA \\(M = (Q, \Sigma, \delta, q\_0, F)\\)，\\(L = L(M)\\) 是否无穷的充要条件为

\\[\exists x \in \Sigma^{\*}. |Q| \le |x| < 2|Q| \wedge \delta(q\_0, x) \in F\\]

</div>


#### Equivalence Problem {#equivalence-problem}

<div class="definition">

**(Product DFA)**

对于两个 DFA \\(M\_1 = (Q\_1, \Sigma, \delta\_1, q\_{01}, F\_1)\\) 和 \\(M\_2 = (Q\_2, \Sigma, \delta\_2, q\_{02}, F\_2)\\)，定义其**乘积 DFA**（product DFA） \\(M\_1 M\_2 = (Q\_1 \times Q\_2, \Sigma \times \Sigma, \delta\_3, [q\_{01}, q\_{02}], F\_3)\\)

其中

-   \\(\delta\_3([x, y], a) = [\delta\_1(x, a), \delta\_2(y, a)]\\)
-   \\(F\_3 = \\{[x, y] | (x \in F\_1) \oplus (y \in F\_2)\\}\\)

</div>

<div class="question">

给定两个正则语言 \\(L\_1, L\_2\\)，问两个语言是否等价？

</div>

<div class="answer">

构建两个语言对应的 DFA 的 product DFA，如果 product DFA 的语言为空（不存在一个句子其中一个自动机接受而另一个不接受），则说明两个语言等价。

</div>


#### Containment Problem {#containment-problem}

<div class="question">

给定两个正则语言 \\(L\_1, L\_2\\)，问是否存在 \\(L\_1 \in L\_2\\)？

</div>

<div class="answer">

同样使用乘积自动机，将终止条件改为：

\\[F\_3 = \\{[x, y] | (x \in F\_1) \wedge (y \notin F\_2)\\}\\]

假设这个乘积自动机存在终止状态，那么说明存在一个 \\(z \in L\_1 \wedge z \notin L\_2\\)。此时原命题不成立；反之乘积自动机为空原命题成立。

</div>


### 封闭性 {#封闭性}

<div class="definition">

**(Closure Property)**

一类语言的**闭包性质**（closure property）指给定这个语言类的一些语言，对于这些语言进行某个操作得到的另一个语言依旧在同一个语言类中。

</div>


#### 保持封闭性的运算 {#保持封闭性的运算}

<div class="theorem">

正则语言在拼接、并、克林闭包下是封闭的。

</div>

<div class="proof">

可以转换成正则表达式，然后直接用正则表达式表达出来。

</div>

<div class="theorem">

正则语言在交集、差集、补集下是封闭的。

</div>

<div class="proof">

利用乘积自动机

-   交集：构建乘积自动机，其中终止状态 \\(F\_3 = \\{[x, y] | x \in F\_1 \wedge y \in F\_2\\}\\)
-   差集：构建乘积自动机，其中终止状态 \\(F\_3 = \\{[x, y] | x \in F\_1 \wedge y \notin F\_2\\}\\)
-   补集：正则语言 \\(L\\) 的补集为 \\(\Sigma^\* - L\\)，由于 \\(\Sigma^\*\\) 是正则语言，因此 \\(L\\) 的补集也是正则语言

</div>

<div class="theorem">

正则语言在逆操作（即字符串反转）下封闭。

</div>

<div class="proof">

利用正则表达式证明。设 RL \\(L\\) 的正则表达式为 \\(E\\)，下面构建它的逆 \\(E^R\\)：

-   如果 \\(E\\) 是字符 \\(a \in \Sigma\\) 或 \\(\varepsilon\\) 或 \\(\emptyset\\)，那么 \\(E^R = E\\)
-   如果 \\(E = F + G\\)，那么 \\(E^R = F^R + G^R\\)
-   如果 \\(E = FG\\)，那么 \\(E^R = (FG)^R = G^R F^R\\)
-   如果 \\(E = F^\*\\)，那么 \\(E^R = (F^R)^\*\\)

根据上面的规则构建的 \\(E^R\\) 依然是正则表达式，因此 \\(E^R\\) 仍然是 RL。

</div>

封闭性可以用来做反证，证明某个语言不是 RL。

<div class="proposition">

令 \\(L\_1 = \\{x | \text{$x$ contains equal numbers of $0$ and $1$}\\}\\)，证明 \\(L\_1\\) 不是正则语言。

</div>

<div class="proof">

令 \\(L\_2 = \\{0^n 1^n | n \ge 0\\}\\)，由泵引理知 \\(L\_2\\) 不是正则语言。

令 \\(L\_3 = \\{0^\*1^\*\\}\\)，显然 \\(L\_3\\) 也是正则语言

假如 \\(L\_1\\) 是正则语言，那么 \\(L\_2 = L\_1 \cap L\_3\\) 也是正则语言，矛盾。因此原命题成立。

</div>


#### 正则代换 {#正则代换}

<div class="definition">

**(正则代换)**

设 \\(\Sigma, \Delta\\) 是两个字母表，映射

\\[f : \Sigma \rightarrow 2^{\Delta^\*}\\]

称为是从 \\(\Sigma\\) 到 \\(\Delta\\) 的**代换**（substitution），其中 \\(2^{\Delta^\*}\\) 表示 \\(\Delta\\) 上的语言组成的集合，\\(f\\) 能将一个字母映射到一个语言。

\\(f\\) 的定义域可以扩展到字符串集合 \\(\Sigma^\*\\) 上，对于 \\(f : \Sigma^\* \rightarrow 2^{\Delta^\*}\\)，满足

\\[f(s)=\begin{cases}
\\{\varepsilon\\}, & s = \varepsilon \\\\
f(x) f(a), & s = xa
\end{cases}\\]

最后，\\(f\\) 的定义域可以扩展到语言集合 \\(2^{\Sigma^\*}\\) 上，对于 \\(f : 2^{\Sigma^\*} \rightarrow 2^{\Delta^\*}\\)，满足

\\[f(L) = \bigcup\_{x \in L} f(x)\\]

</div>

定义域相当于一个大自动机（对于字符串来说是相当于是自动机上的一条路径），然后使用正则代换将这个大自动机中的每个小节点都替换成一个自动机。

例如设 \\(\Sigma = \\{0, 1\\}, \Delta = \\{a, b\\}, f(0) = a, f(1) = b^\*\\)，则

-   \\(f(010) = f(0)f(1)f(0) = ab^\*a\\)
-   \\(f(L(0^\*(0+1)1^\*) = L(a\*(a+b^\*(b^\*)^\*))) = L(a^\*b^\*)\\)

<div class="definition">

设 \\(\Sigma, \Delta\\) 是两个字母表，映射 \\(f : \Sigma \rightarrow 2^{\Delta^\*}\\)。如果对于 \\(\forall a \in \Sigma\\)，\\(f(a)\\) 都是 \\(\Delta\\) 上的 RL，则称 \\(f\\) 是**正则代换**（regular substitution）。

可将 \\(f\\) 进行扩展 \\(f : 2^{\Sigma^\*} \rightarrow 2^{\Delta^\*}\\)：

-   \\(f(\emptyset) = \emptyset, f(\varepsilon) = \varepsilon\\)
-   \\(\forall a \in \Sigma, f(a)\\) 是正则表达式
-   如果 \\(r, s\\) 是 \\(\Sigma\\) 上的正则表达式，则 \\(f(r + s) = f( r) + f(s), f(rs) = f( r)f(s), f(r^\*) = f( r)^\*\\)

</div>

<div class="theorem">

设 \\(\Sigma, \Delta\\) 是两个字母表，映射 \\(f : \Sigma \rightarrow 2^{\Delta^\*}\\) 是正则代换，则 \\(f(L)\\) 也是 RL。

</div>

<div class="proof">

使用归纳法，对 \\(L\\) 对应的正则表达式 \\(r\\) 进行归纳易证。

</div>


#### 同态映射 {#同态映射}

<div class="definition">

设 \\(\Sigma, \Delta\\) 是两个字母表，映射 \\(f : \Sigma \rightarrow \Delta^\*\\)，如果扩展到 \\(f : \Sigma^\* \rightarrow \Delta^\*\\) 上后有

\\[\forall x, y \in \Sigma^\*. f(xy) = f(x) f(y)\\]

则称 \\(f\\) 是从 \\(\Sigma^\*\\) 到 \\(\Delta^\*\\) 的**同态映射**（homomorphism）。

-   对于 \\(L \subseteq \Sigma^\*\\)，其**同态像**为 \\(f(L) = \bigcup\_{x \in L}f(x)\\)
-   对于 \\(w \subseteq \Delta^\*\\)，其**同态原像**（逆同态）为一个集合 \\(f^{-1}(w) = \\{x | f(x) = w \wedge x \in \Sigma^\*\\}\\)

</div>

此处，注意 \\(f(f^{-1}(L)) \ne L\\)，因为有可能 \\(\exists x \in L, \forall y \in \Sigma^{\*}, f(y) \ne x\\)，但是一定有 \\(f(f^{-1}(L)) \subseteq L\\)。

同态映射是正则代换的特例（同态映射可以看成令正则代换的值域为只包含一个句子的语言，那么这个语言一定是正则语言）。

<div class="theorem">

RL 的同态像是 RL。

</div>

<div class="proof">

由于同态映射是正则代换的特例，因此这个显然成立。

</div>

<div class="theorem">

RL 的同态原像是 RL。

</div>

<div class="proof">

设同态映射 \\(f : \Sigma^\* \rightarrow \Delta^\*\\)。DFA \\(M(Q, \Delta, \delta, q\_0, F)\\)，\\(L(M) = L\\)。

则 DFA \\(M'(Q, \Sigma, \delta', q\_0, F)\\)，其中

\\[\delta'(q, a) = \delta(q, f(a))\\]

要证明 \\(L(M) = L(M')\\)，即证明 \\(\delta'(q\_0, x) \in F \Leftrightarrow \delta(q\_0, f(x)) \in F\\)。

下面先证明 \\(\delta(q\_0, f(x)) = \delta'(q\_0, x)\\)，对 \\(|x|\\) 进行归纳：

-   \\(|x| = 0\\)，显然成立
-   设 \\(|x| = |y| = k\\) 的时候成立，那么当 \\(|x| = |ya| = k + 1\\) 时，

    \\[\delta(q\_0, x) = \delta'(q\_0, ya) = \delta'(\delta'(q\_0, y), a) = \delta(\delta(q\_0, f(y)), f(a)) = \delta(q\_0, f(y)f(a)) = = \delta(q\_0, f(x))\\]

</div>
