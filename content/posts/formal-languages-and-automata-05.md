+++
title = "[形式语言] 05 Pushdown Automaton"
author = ["roife"]
date = 2023-10-17
series = ["formal-language-and-automata"]
tags = ["形式语言", "自动机理论", "理论计算机"]
draft = false
+++

## PDA {#pda}


### 定义 {#定义}

RL 可以用一个 DFA 识别，其中 DFA 的每个状态都对应了 RL 的右线性文法 \\(A \rightarrow aB\\) 表示中的一个语法变量，字母表示了 DFA 上的一条边（转移）。

从前面的讨论可知 CFG 可以转换成 GNF 表示，其形式为 \\(A \rightarrow a B\_1 B\_2 \dots B\_n\\)，与右线性文法的区别在于它的右侧有多个需要依次转移的变量。为了识别 CFL，下推自动机在 FA 的基础上增加了一个栈，用于存储需要派生的状态变量。

<div class="definition">

**(Pushdown Automata)**

定义**下推自动机**（Pushdown Automata，PDA）为一个七元组 \\(P = (Q, \Sigma, \Gamma, \delta, q\_0, Z\_0, F)\\) ，其中：

-   \\(Q\\) 是一个有限的**状态**的集合
-   \\(\Sigma\\) 是一个**输入字母表**
-   \\(\Gamma\\) 一个**栈字母表**（stack alphabet）
-   \\(\delta\\) 是一个**状态转移函数**（transition function）
    -   \\(\delta : Q \times (\Sigma \cup \\{\varepsilon\\}) \times \Gamma \rightarrow 2^{Q \times \Gamma^{\*}}\\)
    -   \\(\delta(q, a, Z) = \\{(p\_i, \alpha\_i) | p\_i \in Q, \alpha\_i \in \Gamma^\*\\}\\) 表示 PDA 在状态 \\(q\\) 下且栈顶符号为 \\(Z\\) 时，可以选择将状态变为 \\(p\_i\\)，将 \\(Z\\) 从栈顶弹出并将序列 \\(\alpha\\) 从右到左依次压入栈，然后将读头移动到下一个字符
-   \\(q\_0 \in Q\\) 是起始状态
-   \\(Z\_0 \in \Gamma\\) 是起始符号
-   \\(F \subseteq Q\\) 是接收状态的集合

</div>

如果 \\(\delta(q, a, Z) = \\{(p, \epsilon)\\}\\)，相当于从栈中弹出一个元素。

<div class="definition">

设 PDA \\(M = (Q, \Sigma, \Gamma, \delta, q\_0, Z\_0, F)\\)，\\((q, w, \gamma) \in (Q, \Sigma^{\*}, \Gamma^{\*})\\) 称为 \\(M\\) 的一个**即时描述**（instantaneous description, ID）。它表示 \\(M\\) 处于状态 \\(q\\)；\\(w\\) 是未处理完的字符串，\\(M\\) 正注视着 \\(w\\) 的首字符；\\(\gamma\\) 从左到右是从栈顶到栈底的符号。

-   如果 \\((p, \gamma) \in \delta(q, a, Z)\\)，则 \\((q, aw, Z\beta) \vdash\_M (p, w, y \beta)\\) 表示 \\(M\\) 做了一次**非空移动**
-   如果 \\((p, \gamma) \in \delta(q, \varepsilon, Z)\\)，则 \\((q, w, Z\beta) \vdash\_M (p, w, y \beta)\\) 表示 \\(M\\) 做了一次**空移动**

</div>

同样可以定义 \\(\vdash\_M^n\\)，\\(\vdash\_M^+\\) 和 \\(\vdash\_M^{\*}\\)，没有歧义时可以省略 \\(M\\)。


### 接收 {#接收}

类似 FA，PDA 在接收状态下仍然可以继续工作，PDA 的接收可以有两种定义。

<div class="definition">

设有 PDA \\(M = (Q, \Sigma, \Gamma, \delta, q\_0, Z\_0, F)\\)，则

-   \\(M\\) 用终态接收的语言为 \\(L(M) = \\{w | (q\_0, w, Z\_0) \vdash^\* (p, \varepsilon, \beta) \wedge p \in F\\}\\)
-   \\(M\\) 用空栈接收的语言为 \\(N(M) = \\{w | (q\_0, w, Z\_0) \vdash^\* (p, \varepsilon, \varepsilon)\\}\\)（不需要 \\(p \in F\\)）

</div>

下面是识别语言 \\(L = \\{w 2 w^T | w \in \\{0, 1\\}^{\*}\\}\\) 的一个 PDA 设计：

-   考虑对应的 CFG：\\(G : S \rightarrow 2 | 0S0 | 1S1\\)，将其转化为 GNF \\(G' : S \rightarrow 2 | 0SA | 1SB; A \rightarrow 0; B \rightarrow 1\\)
-   将其转换为 PDA \\(M = (\\{q\_0\\}, \\{0, 1, 2\\}, \\{S, A, B\\}, \delta, q\_0, S, \emptyset)\\)
    -   \\(\delta(q\_0, 0, S) = \\{(q\_0, SA)\\}\\)，\\(\delta(q\_0, 1, S) = \\{(q\_0, SB)\\}\\)，\\(\delta(q\_0, 2, S) = \\{(q\_0, \varepsilon)\\}\\)
    -   \\(\delta(q\_0, 0, A) = \\{(q\_0, \varepsilon)\\}\\)，\\(\delta(q\_0, 1, B) = \\{(q\_0, \varepsilon)\\}\\)
    -   此时是一个空栈接收的语言
-   同时可以将其转换成一个终态接收的语言 \\(M = (\\{q\_0, q\_1\\}, \\{0, 1, 2\\}, \\{S, A, B, Z\\}, \delta, q\_0, Z, \\{q\_1\\})\\)
    -   \\(\delta(q\_0, \varepsilon, Z) = \\{(q\_0, SZ), (q\_1, \varepsilon)\\}\\)
    -   \\(\delta(q\_0, 0, S) = \\{(q\_0, SA)\\}\\)，\\(\delta(q\_0, 1, S) = \\{(q\_0, SB)\\}\\)，\\(\delta(q\_0, 2, S) = \\{(q\_0, \varepsilon)\\}\\)
    -   \\(\delta(q\_0, 0, A) = \\{(q\_0, \varepsilon)\\}\\)，\\(\delta(q\_0, 1, B) = \\{(q\_0, \varepsilon)\\}\\)，\\(\delta(q\_0, \varepsilon, Z\_0) = \\{(q\_0, \varepsilon)\\}\\)


### PDA 与图灵机 {#pda-与图灵机}

\\(\\{w2w^T | w \in \\{0, 1\\}^{\*}\\}\\) 和 \\(\\{a^n b^n\\}\\) 可以用 PDA 模拟弹栈实现，但是 \\(\\{w2w | w \in \\{0, 1\\}^{\*}\\}\\) 和 \\(\\{a^n b^n c^n\\}\\) 则不能用 PDA 构造。

从定义可以看出，一个 PDA 等价于一台拥有两根纸带的“受限图灵机”：在第一根纸带上，图灵机只能从左向右移动并且不能更改纸带；在第二根纸带上，图灵机只能删除纸带最左边的元素（弹出）或在纸带最左边添加元素（压入）。

从 PDA 的定义可以看出，与 FA 相比，PDA 多了存储数据的能力；但是与图灵机相比，它对数据的读取顺序有限制，而且只能读取一次。尽管可以设计 \\(\delta\\) 使得 PDA 在弹出符号后重新压回去，但是这会导致 PDA 无法解析底层的符号。

PDA 之所以比图灵机弱，是因为它弹出操作会删除数据，因此添加一根纸带用于存储删除值的 PDA 可以等价模拟图灵机。在这个模型下 PDA 相当于有三根纸带：一根只读的输入带和两个栈纸带。PDA 首先从输入带中读入元素并全部压入第一个栈中，然后就可以像图灵机一样进行操作：

-   向左移动等价于弹出第一个栈的元素，并压入第二个栈；向右移动则相反
-   写入操作对应弹出元素，并压入想要写入的元素


## PDA 的变形 {#pda-的变形}


### 确定性 PDA {#确定性-pda}


#### 定义 {#定义}

上面描述的实际上是一个非确定性的 PDA，因为状态转移的结果是一个集合，下面定义了确定性的 PDA。

<div class="definition">

**(Deterministic PDA, DPDA)**

**确定的 PDA** \\(M = (Q, \Sigma, \Gamma, \delta, q\_0, Z\_0, F)\\) 是满足下面条件的 PDA：

\\[\forall (q, a, Z) \in Q \times \Sigma \times \Gamma, |\delta(q, a, Z)| + |\delta(q, \varepsilon, Z)| \le 1\\]

</div>


#### DPDA 的接收与 DCFL {#dpda-的接收与-dcfl}

在 DPDA 中，空栈接收和终态接收所描述的语言类并不等价（对 PDA 来说是等价的）。例如终态接收的 DPDA 可以描述 \\(0^n\\)，但是空栈接收的 DPDA 无法描述。这是因为空栈接收的 DPDA 如果接受一门语言，那么对于这门语言中任意两个字符串 \\(x, y\\)，满足 \\(\forall z \in \Sigma^\*. xz \ne y\\)，即任意一个字符串都不是另一个字符串的前缀（因为空栈接收的 DPDA 会提前终止）。所以终态接收的 DPDA 更加灵活，能够接收的语言更多。

通常使用终态接收的 PDA 定义确定性上下文无关语言（DCFL）。在编译器的设计中，识别的实际上也是 DCFL。当 DPDA 只有一个状态时，它描述的就是 \\(LL(1)\\) 语言。

DPDA 描述的 CFL 一定是无二义性的（但是无二义性的语言不一定可以用 DPDA 描述）。


#### DPDA 与 NPDA {#dpda-与-npda}

虽然 DFA 可以用子集枚举的方式模拟 NFA，例如用 \\(\\{1, 2\\}\\) 来模拟同时走两个状态，但是在 DPDA 中走一步还伴随了对栈的操作，而**对栈的操作无法利用子集枚举来同时模拟多个操作**，即在 DPDA 中每一步对栈的操作都是**确定且不可逆**的。在利用子集枚举法模拟 NFA 时，NPDA 在多个状态下对栈的不同操作被收束到 DPDA 下对栈的唯一操作，这使得 DPDA 丧失了灵活性。

可以将 PDA 的栈看作是“全局状态”的一部分（当然这样的“全局状态”的数量是无限的），这样就会发现 DPDA 无法实现 NPDA 的模拟。

而 NFA 由于状态机有多个方向可以选择，每个方向对栈可以有不同的操作，因此能力更强。所以 DPDA 接收的语言集合是 NPDA 的子集。例如偶数长度的回文串 \\(S \rightarrow 0S0 | 1S1 | \varepsilon\\) 无法被 DPDA 接接收，下面是一个简单的证明：

-   假设 DPDA 能够接收 \\(S \rightarrow 0S0 | 1S1 | \varepsilon\\)，那么它就能接收 \\(s\_1 = 0^{n}110^{n}\\) 和 \\(s\_2 = 0^n110^n0^n110^n\\)
-   经过上面的讨论得知终态接收的 DPDA 描述能力更强，因此不妨使用终态接收的 DPDA 构造
-   DPDA 在接收 \\(s\_1\\) 时，由于状态机的状态数量和栈符号字母表数量是有限的，因此它必须通过压栈的方式记录 \\(n\\) 的数量，并且在遇到第二个 \\(0^n\\) 时弹出栈中的符号来验证是否接收 \\(s\_1\\)
-   由于 DPDA 每一步都是确定的，因此在经过 \\(s\_2\\) 的前半部分时，其经过的全局状态一定与 \\(s\_1\\) 的接收过程相同
-   但是由之前的讨论知，此时 DPDA 已经弹出了栈中的所有符号，因此它无法判定 \\(s\_2\\) 的前半部分与后半部分是否回文

在下一章讨论 DCFL 的性质还有一个严格的证明。

在这个例子中，NPDA 可以在每一步选择两个方向：开始弹栈，或继续压栈。但是 DPDA 在每一步只能做一个抉择，而它并不能判断在哪一步开始弹栈。而对于普通的 \\(0^n10^n\\)，DPDA 可以在识别到 \\(1\\) 的时候判断跨过了中点时就开始弹栈。


### Generalized PDA {#generalized-pda}

<div class="definition">

广义下推自动机（generalized PDA, GPDA）定义为一个七元组 \\(M = (Q, \Sigma, \Gamma, \delta, Z\_0, q\_0, F)\\)，其中 \\(\delta : Q \times (\Sigma \cup \\{\varepsilon\\}) \times \Gamma^{\*} \rightarrow 2^{Q \times \Gamma^{\*}}\\)

</div>

GPDA 的特殊之处在于每次可以向栈中压入一系列字符或弹出一系列字符。

不难证明 GPDA 与 PDA 等价：

-   PDA 显然是 GPDA
-   对于 PDA 中的特殊操作 \\(\delta(q, w, x\_1 x\_2 \dots x\_n) = (p, y\_1 y\_2 \dots y\_m)\\)，定义

    \\[\delta'(q, w, x\_1) = (p\_1, \varepsilon)\\]
    \\[\delta'(p\_1, \varepsilon, x\_2) = (p\_2, \varepsilon)\\]
    \\[\dots\\]
    \\[\delta'(p\_{m-1}, \varepsilon, x\_m) = (p\_m, \varepsilon)\\]
    \\[\delta'(p\_{m}, \varepsilon, \varepsilon) = (p\_{m+1}, y\_n)\\]
    \\[\delta'(p\_{m+1}, \varepsilon, \varepsilon) = (p\_{m+1}, y\_{n-1})\\]
    \\[\dots\\]
    \\[\delta'(p\_{m+n-1}, \varepsilon, \varepsilon) = (p, y\_1)\\]


### Counter Automaton {#counter-automaton}

Counter automaton 是一类受限的 PDA，其中它只能向纸带上打印唯一的一种符号，即 \\(|\Gamma| = 1\\)。

Counter automaton 等价于带了一个额外的计数器（只能记录非负数）的 FA，这使其能够识别类似于 \\(0^n 0^n\\) 这样的语言，但是由于计数器只能记录一个非负数，因此无法识别 \\(0^n1^m1^m0^n\\) 这样的语言。


### Queue Automaton {#queue-automaton}

Queue automaton 又称 pullup automaton（PUA）。相比 PDA，QA 能够

<div class="definition">

一个 queue automaton 可以用一个六元组 \\(M = (Q, \Sigma, \Gamma, \\$, S, \delta)\\) 描述：

-   \\(Q, S\\) 的定义同 PDA
-   \\(\Sigma \subset \Gamma\\) 是有限的输入字母表
-   \\(\Gamma\\) 是有限的队列字母表
-   \\(\\$ \in \Gamma \backslash \Sigma\\) 是队列的起始标记
-   \\(\delta : Q \times \Gamma \rightarrow Q \times \Gamma^{\*}\\) 是状态转移函数
    -   队列的状态可以用 \\((p, \alpha)\\) 表示，前者是当前的状态，后者是当前的队列
    -   \\(\delta(p, A\alpha) = (q, \alpha \gamma)\\) 表示在状态 \\(p\\) 下；队列为 \\(A\alpha\\)，头部为 \\(A\\)；然后取出字符 \\(A\\)，转移到状态 \\(q\\)，并在队尾压入 \\(\gamma\\)
-   接收状态定义为队列为空

</div>

可以证明 QA 等价于图灵机。显然图灵机可以模拟 QA，因此只需要用 QA 模拟图灵机即可：

-   首先将图灵机的纸带复制到 QA 的队列内，并且在首尾添加两个符号：图灵机读头符号 \\(\\$\\) 和纸带分隔符 \\(\\#\\)
-   对于图灵机的每一次状态转移，QA 都会遍历两趟纸带（从开头到第一次遇到 \\(\\#\\)）
-   状态用  \\((q, 0/1, x, L/R, z)\\) 表示，一开始状态是 \\((q\_0, 0, \bot, ?, \bot)\\) ，其中 \\(\bot \notin \Sigma\\)
    -   第一个 \\(q\\) 表示图灵机的状态
    -   第二个 \\(0\\) 表示这是第一趟，\\(1\\) 表示这是第二趟
    -   第三个 \\(x\\) 在第一趟遇到读头前存储的是上一个字符，遇到读头后存储读头前一个位置的字符，可以是 \\(\bot\\)
    -   第四个 \\(L/R\\) 表示读头在第二趟时是左移还是右移，\\(?\\) 表示还没遇到第一趟的读头，\\(!\\) 表示刚经过第一趟的读头
    -   第五个 \\(z\\) 用于记录第二趟遇到读头前的上一个字符，可以是 \\(\bot\\)
    -   第二个和第四个位置决定了当下的操作，第一个和第三个和第五个位置用于记录
-   第一趟遍历处理转移（下面所说的读取指取出队首并转移；打印指把字符放到队尾，\\(\bot\\) 不打印）
    -   开始的状态是 \\((q, 0, x / \bot, ?, \bot)\\)
        -   如果当前字符 \\(y \in \Sigma\\)，转移到 \\((q, 0, y, ?, \bot)\\)，并打印 \\(x\\)
        -   遇到读头时，状态是 \\((q, 0, x, ?, \bot)\\)，当前状态中的第三个位置 \\(x\\) 是读头前的一个字符。此时不放字符，转移到 \\((q, 0, x, !, \bot)\\)，读取下一个字符
        -   由于还没遇到读头，当前字符不可能是 \\(\\#\\)
    -   此时状态形如 \\((q, 0, x, !, \bot)\\)，检测到读头，模拟图灵机的一次操作，设状态转移到 \\(p\\)，打印 \\(y\\)，读头移动为 \\(L/R\\)
        -   将 \\(xy\\) 放到队列中，状态转移到 \\((p, 0, x, L/R, \bot)\\)，并继续读入字符
    -   经过读头后，状态形如 \\((q, 0, x, L/R, \bot)\\)，此时如果当前位置的字符 \\(y \in \Sigma\\)，则打印，且状态不转移
        -   如果当前字符是 \\(\\#\\)，状态转移到 \\((q, 1, x, L/R, \bot)\\)，并打印 \\(\\#\\)
-   第二趟遍历打印读头
    -   开始状态是 \\((q, 1, x, L/R, z/\bot)\\)
        -   如果当前位置的字符 \\(y \in \Sigma\\)，则状态转移到 \\((q, 1, x, L/R, y)\\)，并打印 \\(z\\)
        -   直到遇到读头
            -   如果状态是 \\((q, 1, x, L, z)\\) 则打印 \\(\\$x\\)，状态转移到 \\((q, 1, x, L, \bot)\\)
            -   如果状态是 \\((q, 1, x, R, z)\\) 则，则打印 \\(x\\) 并转移到 \\((q, 1, x, ?, \bot)\\)
    -   此时状态可能是 \\((q, 1, x, ?, \bot)\\)，表示恰好在读头右一个位置，设当前字符为 \\(y\\)，打印 \\(y\\$\\)，并转移到 \\((q, 1, x, R, \bot)\\)
    -   最后遇到 \\(\\#\\)，状态是 \\((q, 1, x, L/R, z)\\)，打印 \\(z\\#\\)，状态转移到 \\((q, 0, x, ?, \bot)\\)
-   如果到了图灵机的接收状态，则后面的指令就是一直读取直到清空队列


## PDA 的性质 {#pda-的性质}


### 预先放置 {#预先放置}

<div class="theorem">

给定 PDA \\(P\\)，如果 \\((q, x, \alpha) \vdash^{\*} (p, y, \beta)\\)，则 \\(\forall w \in \Sigma^{\*}, \gamma \in \Gamma^{\*}. (q, xw, \alpha \gamma) \vdash^{\*} (p, yw, \beta \gamma)\\)。

</div>

<div class="theorem">

给定 PDA \\(P\\)，如果 \\((q, xw, \alpha) \vdash^{\*} (p, yw, \beta)\\)，则 \\((q, x, \alpha) \vdash^{\*} (p, y, \beta)\\)。

</div>

注意删除相同的部分栈底元素可能会对自动机造成影响。


### 空栈接收与终态接收等价 {#空栈接收与终态接收等价}

首先证明任意终态接收的 PDA 可以转换为空栈接收的 PDA。

<div class="theorem">

对于任意 PDA \\(M\_1\\)，存在 PDA \\(M\_2\\) 使得 \\(L(M\_1) = N(M\_2)\\)

</div>

<div class="proof">

下面使用构造证明。

> 这个证明的核心在于两点
>
> 1.  \\(M\_1\\) 进入终止状态后，要清空栈来接收（下面用 \\(q\_{\varepsilon}\\) 来解决）
>     -   如果 \\(M\_2\\) 进入了 \\(q\_\varepsilon\\)，则用空移动可以清栈，根据 NFA 的性质，此时输入也被读完才能接收
> 2.  \\(M\_1\\) 没到终止状态，\\(M\_2\\) 栈空时不能误接收（下面用 \\(q\_{02}, Z\_{02}\\) 来解决）

设 PDA \\(M\_1 = (Q, \Sigma, \Gamma, \delta\_1, q\_{01}, Z\_{01}, F)\\)，下面构造 \\(M\_2 = (Q \cup \\{q\_{02}, q\_{\varepsilon}\\}, \Sigma, \Gamma \cup \\{Z\_{02}\\}, \delta\_2, q\_{02}, Z\_{02}, F)\\)。并根据下面规则构建 \\(\delta\_{2}\\)。

-   \\(M\_2\\) 启动后，立即进入 \\(M\_1\\) 的初始 ID \\(\delta\_2(q\_{02}, \varepsilon, Z\_{02}) = \\{(q\_{01}, Z\_{01}Z\_{02})\\}\\)
-   在 \\(M\_1\\) 的非空移动，\\(M\_2\\) 直接模拟 \\(\forall (q, a, Z) \in Q \times \Sigma \times \Gamma. \delta\_2(q, a, Z) = \delta\_1(q, a, Z)\\)
-   在 \\(M\_1\\) 非终态时的空移动也可以直接模拟 \\(\forall(q, Z) \in (Q - F) \times \Gamma. \delta\_2(q, \varepsilon, Z) = \delta\_2(q, \varepsilon, Z)\\)
-   当 \\(M\_1\\) 进入终态时进行空移动，\\(M\_2\\) 要额外模拟清栈 \\(\forall(q, Z) \in F \times \Gamma. \delta\_2(q, \varepsilon, Z) = \delta\_1(q, \varepsilon, Z) \cup (q\_\varepsilon, \varepsilon)\\)
-   \\(M\_1\\) 栈空并且进入终态，\\(M\_2\\) 也一定终止 \\(\delta\_2(q, \varepsilon, Z\_{02}) = \\{(q\_\varepsilon, \varepsilon)\\}\\)
-   \\(M\_2\\) 清栈后可以接收 \\(\forall Z \in \Gamma \cup \\{Z\_{02}\\}. \delta\_2(q\_{\varepsilon}, \varepsilon, Z) = \\{(q\_{\varepsilon}, \varepsilon)\\}\\)

下面证明 \\(L(M\_1) = N(M\_2)\\)。

-   首先证明 \\(L(M\_1) \subseteq N(M\_2)\\)
    -   设 \\(x \in L(M\_1)\\)，则 \\((q\_{01}, x, Z\_{01}) \vdash\_{M\_1}^\* (q, \varepsilon, \gamma)\\)。由于 \\(Z\_{02}\\) 与 \\(M\_1\\) 无关，因此有

        \\[(q\_{01}, x, Z\_{01}Z\_{02}) \vdash\_{M\_1}^{\*} (q, \varepsilon, \gamma Z\_{02})\ (q \in F)\\]

    -   根据定义，\\(M\_2\\) 能模拟 \\(M\_1\\) 的所有移动，并且在 \\(M\_{01}\\) 的终态清栈，有

        \\[(q\_{01}, x, Z\_{01}Z\_{02}) \vdash\_{M\_2}^{\*} (q, \varepsilon, \gamma Z\_{02}) \vdash\_{M\_2}^{\*} (q\_{\varepsilon}, \varepsilon, \varepsilon) \ (q \in F)\\]

    -   又因为 \\((q\_{02}, x, Z\_{02}) \vdash\_{M\_2} (q\_{01}, x, Z\_{01}Z\_{02})\\)，则

        \\[(q\_{02}, x, Z\_{02}) \vdash\_{M\_2} (q\_{01}, x, Z\_{01}Z\_{02}) \vdash\_{M\_2}^{\*} (q, \varepsilon, \gamma Z\_{02}) \vdash\_{M\_2}^{\*} (q\_{\varepsilon}, \varepsilon, \varepsilon) \ (q \in F)\\]

    -   即 \\(x \in N(M\_2)\\)

-   然后证明 \\(N(M\_2) \subseteq L(M\_1)\\)
    -   设 \\(x \in N(M\_2)\\)，将上面的过程反推即可：此时 \\(M\_2\\) 最后必须进入清栈的状态且读完 \\(x\\)，因此 \\(M\_1\\) 必然进入终态且读完 \\(x\\)，即 \\(M\_1\\) 也接收 \\(x\\)

</div>

下面证明反方向：

<div class="theorem">

对于任意 PDA \\(M\_1\\)，存在 PDA \\(M\_2\\) 使得 \\(N(M\_1) = L(M\_2)\\)

</div>

<div class="proof">

类似的，需要通过构造并证明等价性。

> 这个证明的核心在于提前放一个哨兵 \\(Z\_{02}\\) 在 \\(M\_2\\) 的栈中。在接收过程中发现栈顶是 \\(Z\_{02}\\)，则说明栈空了，那么 \\(M\_2\\) 应当立即进入终态。

设 PDA \\(M\_1 = (Q, \Sigma, \Gamma, \delta\_1, q\_{01}, Z\_{01}, F)\\)，下面构造 \\(M\_2 = (Q \cup \\{q\_{02}, q\_{f}\\}, \Sigma, \Gamma \cup \\{Z\_{02}\\}, \delta\_2, q\_{02}, Z\_{02}, \\{q\_f\\})\\)。并根据下面规则构建 \\(\delta\_{2}\\)。

-   \\(M\_2\\) 启动后，开始模拟 \\(M\_1\\) 的栈 \\(\delta\_2(q\_{02}, \varepsilon, Z\_{02}) = \\{(q\_{01}, Z\_{01}Z\_{02})\\}\\)
-   在 \\(M\_1\\) 的非空移动，\\(M\_2\\) 直接模拟 \\(\forall (q, a, Z) \in Q \times \Sigma \times \Gamma. \delta\_2(q, a, Z) = \delta\_1(q, a, Z)\\)
-   如果 \\(M\_1\\) 的栈空时，立即进入终态 \\(\delta\_2(q, \varepsilon, Z\_{02}) = \\{(q\_f, \varepsilon)\\}\\)

</div>


### PDA 与 CFG 等价 {#pda-与-cfg-等价}

从 CFL 转换到 PDA 比较简单，只需要考虑 CFG 的 GNF 即可。

<div class="theorem">

对于任意 CFL \\(L\\)，存在 PDA \\(M\\)，使得 \\(N(M) = L\\)。

</div>

<div class="proof">

设 CFL 对应 GNF \\(G(V, T, P, S)\\)，使得 \\(L(G) = L\\)。

下面构造一个空栈接收的 PDA \\(M = (\\{q\\}, T, V, \delta, q, S, \emptyset)\\)，其中

\\[\forall A \in V, a \in T. \delta(q, a, A) = \\{(q, \gamma) | A \rightarrow a \gamma \in P\\}\\]

下面证明 \\(L(M) = L(G) = L\\)，设 \\(w \in L\\)，只要证明

\\[(q, w, S) \vdash\_M^n (q, \varepsilon, \alpha) \Leftrightarrow S \xRightarrow{n} wa \in P\\]

-   首先证明充分性，对 \\(|w|\\) 进行归纳
    -   当 \\(n = 1\\) 时，\\((q, a, S) \vdash\_M^n (q, \varepsilon, \alpha)\\)，此处 \\(a \in T\\)，则 \\((q, \alpha) \in \delta(q, a, S)\\)。根据定义，有 \\(S \rightarrow a \alpha \in P\\)，因此 \\(S \Rightarrow a \alpha\\)。
    -   设 \\(n = k\\) 时成立，当 \\(n = k + 1\\) 时，有 \\(w = xa, |x| = k, a \in T\\) 使得

        \\[(q, w, S) = (q, xa, S) \vdash\_M^n (q, a, A \beta\_1) \vdash\_M (q, \varepsilon, \beta\_2 \beta\_1) = (q, \varepsilon, \alpha)\\]

        因此 \\((q, \beta\_2) \in \delta(q, a, A)\\)，根据定义有 \\(A \rightarrow a \beta\_2 \in P\\)。又根据归纳假设有 \\((q, xa, S) \vdash\_M^n (q, a, A \beta\_1) \Rightarrow S \xRightarrow{n} x A \beta\_1 \in P\\)。因此有

        \\[S \xRightarrow{n} x A \beta\_1 \Rightarrow xa \beta\_2 \beta\_1 = xa \alpha = w\alpha \\]

        假设成立。

-   然后证明必要性，同样用归纳的方法
    -   当 \\(n = 1\\) 时，\\(S \Rightarrow w \alpha\\)，其中 \\(w \in T \wedge S \rightarrow w \alpha \in P\\)，根据定义有 \\((q, \alpha) \in \delta(q, w, S)\\)，因此 \\((q, w, S) \vdash\_M (q, \varepsilon, \alpha)\\)，成立
    -   设 \\(n = k\\) 时成立，当 \\(n = k + 1\\) 时，设 \\(S \xRightarrow{k} xA\beta\_1 \Rightarrow xa \alpha = xa\beta\_2\beta\_1\\)，从中可知
        \\[A \rightarrow \alpha \beta\_2 \in P\\]

        因此根据定义有 \\((q, \beta\_2) \in \delta(q, a, A)\\)，即

        \\[(q, a, A) \vdash\_M (q, \varepsilon, \beta\_2)\\]

        又根据归纳假设及 \\(S \xRightarrow{k} xA\beta\_1\\) 有

        \\[(q, xa, S) \vdash\_M^k (q, a, A\beta\_1)\\]

        因此有

        \\[(q, xa, S) \vdash\_M^k (q, a, A\beta\_1) \vdash\_M (q, \varepsilon, \beta\_2 \beta\_1) = (q, \varepsilon, \alpha)\\] 成立

综上所述，下面的结论成立

\\[(q, w, S) \vdash\_M^n (q, \varepsilon, \alpha) \Leftrightarrow S \xRightarrow{n} wa \in P\\]

注意到 \\(\alpha\\) 的任意性，因此

\\[(q, w, S) \vdash\_M^n (q, \varepsilon, \varepsilon) \Leftrightarrow S \xRightarrow{n} w \in P\\]

即 \\(N(M) = L(G)\\)

值得注意的是，这里最后还要考虑 \\(\varepsilon \in L\\) 的情况。首先构造 \\(M = (Q, \Sigma, \Gamma, \delta, q\_0, Z\_0, \emptyset)\\) 使得 \\(N(M) = L - \\{\varepsilon\\}\\)，然后令

\\[M' = (Q \cup \\{q\_\varepsilon\\}, \Sigma, \Gamma \cup \\{Z\_\varepsilon\\}, \delta', q\_\varepsilon, Z\_\varepsilon)\\]

令

\\[\delta(q, a, Z) =
\begin{cases}
\\{(q\_\varepsilon, \varepsilon), (q\_0, Z\_0)\\}, & a = \varepsilon \\\\
\delta(q, a, Z), & a \ne \varepsilon
\end{cases}\\]

则 \\(N(M') = N(M) \cup \\{\varepsilon\\}\\)

</div>

从 PDA 转换到 CFL 要复杂一些。考虑 PDA 的一次移动 \\(\delta(q, a, A) \ni (q\_1, A\_1 A\_2 \dots A\_n)\\) 中表示 \\(M\\) 在状态 \\(q\\) 下，栈顶字符为 \\(A\\)，读入一个字符 \\(a\\) 可以转移到 \\(q\_1\\)，并压入 \\(A\_1 A\_2 \dots A\_n\\)。类似 GNF 的想法，应该设计为 \\([q, a] \rightarrow a [q\_1, A\_1 A\_2 \dots A\_n]\\)。

但是这样设计的问题在于无法给出 \\([q, A\_1 A\_2 \dots A\_n] \rightarrow \dots\\)。注意到这里的 \\(A\_1 A\_2 \dots A\_n\\) 压入栈后，下一次转移 PDA 只能看到栈顶的 \\(A\_1\\)，因此在设计状态时，可以将其拆分开来，一个状态只包含一个符号（每次只压入一个符号），形如 \\([q,A] \rightarrow a[q\_1, A\_1][q\_2, A\_2] \dots [q\_n, A\_n]\\)。这里的 \\([q\_k, A\_k]\\) 表示当 \\(1 \le i \le k\\) 解析完成后，栈顶是 \\(A\_i\\)，状态是 \\(q\_i\\)。

这样设计带来了新的问题：在 PDA 工作时，弹出一个符号后可能压入新的一系列符号，并进行状态转移，而 \\([q\_i, A\_i] [q\_{i+1}, A\_{i+1}]\\) 表示弹出 \\(A\_i\\) 压入新符号前的状态是 \\(q\_i\\)，处理新符号后的状态是 \\(q\_{i+1}\\)。但是实际过程中并不能保证这一点，有可能中间转移到其他状态了。为了保证在 \\(q\_i\\) 处理 \\(A\_i \xRightarrow{k} w\\) 完成后，转移到 \\(q\_{i+1}\\) 再对 \\(A\_{i+1}\\) 进行处理，这里考虑将非终结符表示成：

\\[[q\_i, A\_i, q\_{i+1}]\\]

这表示当前状态 \\(q\_i\\)，栈顶为 \\(A\_i\\)，当前的栈顶和压入的新符号完全弹出（即栈顶变成 \\(A\_{i+1}\\) 时）时状态为 \\(q\_{i+1}\\)。即利用 \\(q\_i \rightarrow q\_{i+1}\\) 之间产生的序列来弹出 \\(A\_i\\)。

<div class="theorem">

对于任意 PDA \\(M\\)，存在 CFG \\(G\\) 使得 \\(L(G) = N(M)\\)。

</div>

<div class="proof">

设 \\(M = (Q, \Sigma, \Gamma, \delta, q\_0, Z\_0, \emptyset)\\)，取 CFG \\(G = (V, \Sigma, P, S)\\)，其中

\begin{aligned}
V =  \\{& S\\} \cup Q \cup \Gamma \cup Q \\\\
P =  \\{& S \rightarrow [q\_0, Z\_0, q] | q \in Q \\} \\\\
  \cup  \\{& [q, A, q\_{n+1}] \rightarrow a[q\_1, A\_1, q\_2][q\_2, A\_2, q\_3] \dots [q\_n, A\_n, q\_{n+1}] \\\\
       & \quad | (q\_1, A\_1 A\_2 \dots A\_n) \in \delta(q, a, A) \wedge a \in \Sigma \cup \\{\varepsilon\\}, q\_i \in Q]\\} \\\\
  \cup  \\{& [q, A, q\_1] \rightarrow a | (q\_1, \varepsilon) \in \delta(q, a, A)\\}
\end{aligned}

下面证明 \\(L(G) = N(M)\\)，即证明

\\[[q, A, p] \xRightarrow{\*} x \Leftrightarrow (q, x, A) \vdash^\* (p, \varepsilon, \varepsilon)\\]

-   首先证明充分性。设 \\([q, A, p] \xRightarrow{n} x\\)，对 \\(n\\) 进行归纳
    -   当 \\(n = 1\\) 时，必有 \\(x \in \Sigma \cup \\{\varepsilon\\}\\)，因此 \\([q, A, p] \rightarrow x \in P\\)，根据定义有 \\((p, \varepsilon) \in \delta(q, a, A)\\)，即 \\((q, a, A) \vdash (p, \varepsilon, \varepsilon)\\)，成立
    -   设 \\(n \le k\\) 时结论成立，即 \\(([q, A, p] \xRightarrow{i} x) \Leftrightarrow ((q, x, A) \vdash^\* (p, \varepsilon, \varepsilon))\ (1 \le i \le n)\\)
    -   则当 \\(n = k + 1\\) 时，有

        \\[[q, A, p] \Rightarrow a[q\_1, A\_1, q\_2][q\_2, A\_2, q\_3] \dots [q\_n, A\_n, q\_{n+1}] \xRightarrow{k} a x\_1 x\_2 \dots x\_n\\]

        根据定义有 \\((q\_1, A\_1 A\_2 \dots A\_n) \in \delta(q, a, A)\\)。

        设 \\([q\_i, A, q\_{i+1}] \xRightarrow{k\_i} x\_i\ (1 \le i \le n)\\) 且 \\(\Sigma k\_i = k\\)。由归纳假设有 \\((q\_i, x\_i, A\_i) \vdash^\* (q\_{i+1}, \varepsilon, \varepsilon)\\)。

        因此

        \begin{aligned}
        (q, a x\_1 x\_2 \dots x\_n, A)
        & \vdash (q\_1, x\_1 x\_2 \dots x\_n, A\_1 A\_2 \dots A\_n) \\\\
        & \vdash^\* (q\_2, x\_2 \dots x\_n, A\_2 \dots A\_n) \\\\
        & \vdash^\* \dots \\\\
        & \vdash^\* (q\_n, x\_n, A\_n) \\\\
        & \vdash^\* (q\_{n+1}, \varepsilon, \varepsilon)
        \end{aligned}

        成立
-   下面证明必要性。设 \\((q, x, A) \vdash^n (p, \varepsilon, \varepsilon)\\)，对 \\(n\\) 进行归纳
    -   当 \\(n = 1\\) 时，\\((q, a, A) \vdash (p, \varepsilon, \varepsilon)\\)，即 \\(\delta(q, a, A) \ni (p, \varepsilon)\\)，根据定义 \\([q, A, p] \rightarrow a \in P\\)，成立
    -   设当 \\(n = k\\) 时成立，即 \\((q, x, A) \vdash^k (p, \varepsilon, \varepsilon) \Rightarrow [q, A, p] \xRightarrow{k} x\\)
    -   则当 \\(n = k + 1\\) 时，设 \\(x = a x\_1 x\_2 \dots x\_n\\)，则

        \\[(q, x, A) = (q, a x\_1 x\_2 \dots x\_n, A) \vdash (q, x\_1 x\_2 \dots x\_n, A\_1 A\_2 \dots A\_n)\\]

        其中 \\((q\_i, x\_i, A\_i) \vdash^{k\_i} (p, \varepsilon, \varepsilon)\\)，则 \\([q\_i, A\_i, q\_{i+1}] \xRightarrow{k\_i} x\_i\\)

        由于 \\((q, x, A) \vdash (q, \varepsilon, A\_1 A\_2 \dots A\_n)\\)，因此有 \\(\delta(q, x, A) \ni (q\_1, A\_1 A\_2 \dots A\_n)\\)，根据定义有

        \\[[q, A, q\_{n+1}] \rightarrow a[q\_1, A\_1, q\_2][q\_2, A\_2, q\_3] \dots [q\_n, A\_n, q\_{n+1}] \in P\\]

        综上，有

        \begin{aligned}
        [q, A, q\_{n+1}] & \xRightarrow a[q\_1, A\_1, q\_2][q\_2, A\_2, q\_3] \dots [q\_n, A\_n, q\_{n+1}] \\\\
                        & \xRightarrow{\*} a x\_1 [q\_2, A\_2, q\_3] \dots [q\_n, A\_n, q\_{n+1}] \\\\
                        & \dots \\\\
                        & \xRightarrow{\*} a x\_1 x\_2 \dots x\_n = x
        \end{aligned}

        成立。

综上，原命题成立

</div>
