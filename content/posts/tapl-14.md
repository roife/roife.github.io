+++
title = "[TaPL] 14 Exceptions"
author = ["roife"]
date = 2021-10-05
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论", "程序语义", "STLC"]
draft = false
+++

程序在运行过程中会发生各种异常情况，此时可以通过 `Optional` 类型去处理，但是这种方式要求每个 caller 都要参与到错误的处理中。而使用异常机制则可以直接将 exceptions 交给 exceptions handler 处理（此时程序的 control flow 发生变化），或者直接终止程序。

本章基于 STLC 和一些扩展类型，并且分成三类讨论：遇到异常直接终止程序、将异常移交 handler 处理以及将异常信息传递给 handler。


## Raising Exceptions {#raising-exceptions}

{{< figure src="/img/in-post/post-tapl/14-1-errors.png" caption="<span class=\"figure-number\">Figure 1: </span>Errors" >}}

首先定义 `error`，其 evaluation rules 使得程序只要一遇到 `error` 就会退出。

这里只把 `error` 定义为 term 而不是 value，这样消除了规则调用的二义性。如果 `error` 是 value 的话，那么对于 \\((\lambda x : \operatorname{\mathtt{Nat}}. 0)\ \operatorname{\mathtt{error}}\\) 既可以调用 `E-AppAbs` 又可以调用 `E-AppErr2`。同样 `E-AppErr2` 也要求左侧为 \\(v\_1\\)，防止有二义性。

在加了 exceptions 类型后，preservation property 和原来一样（即 evaluation 不改变类型），但是 progress property 会发生变化（因为加入了 `error`，结果不一定再是 value）。

<div class="definition">

**(Progress)**

Suppose \\(t\\) is a closed, well-typed normal form. Then either \\(t\\) is a value or \\(t=\operatorname{\mathtt{error}}\\).

</div>


### Syntax-directed {#syntax-directed}

<div class="definition">

**(Syntax-directed)**

符合 syntax directed 的规则需要满足两点要求：

-   规则使用没有二义性（对于一个 term 只能使用一种规则，不会出现两种规则可以同时用于一个 term 的情况）
-   通过语法就可以进行推断（例如类型推断 \\(t\_1\ t\_2\\) 只需要知道二者的类型就可以知道这个 term 的类型）

</div>

\\[
\Gamma \vdash \operatorname{\mathtt{error}} : T
\\]

上面这条规则使得 evaluation rules 不再是 syntax directed 的了，并导致了 uniqueness of types theorem 失效。`T-Error` 表明 `error` 可以是任何类型。例如在 \\((\lambda x : \operatorname{\mathtt{Bool}}. x)(\operatorname{\mathtt{error}}\ \operatorname{\mathtt{true}})\\) 中 `error` 的类型为 \\(\operatorname{\mathtt{Bool}} \rightarrow \operatorname{\mathtt{Bool}}\\)。但是 `T-Error` 这个打破了“所有 `term` 都只有一个类型”的规则，这一点会在后面解决：

-   在支持 subtyping 的系统中，可以令 \\(\operatorname{\mathtt{error}} : \bot\\)
-   在支持 parametric polymorphism 的系统中，可以令 \\(\operatorname{\mathtt{error}} : \forall x. x\\)

<div class="question">

能否通过手动给 `error` 标注类型来解决问题？

</div>

<div class="answer">

`error` 不能是某个具体的类型（即不能通过 ascription 的手段去解决 exceptions 的问题），必须是 \\(T\\)，否则会违反 preservation 性质。因为在传递 `error` 的过程中，`error` 的类型会随着上下文的改变而发生改变。

例如在 \\((\lambda x : \operatorname{\mathtt{Nat}}. x) ((\lambda y : \operatorname{\mathtt{Bool}}. 5) (\operatorname{\mathtt{error}}\ \operatorname{\mathtt{as}}\ \operatorname{\mathtt{Bool}}));\\) 中，进行外部函数的规约时就会发生错误。

</div>


## Handling Exceptions {#handling-exceptions}

{{< figure src="/img/in-post/post-tapl/14-2-error-handling.png" caption="<span class=\"figure-number\">Figure 2: </span>Error Handling" >}}

`error` 求值的过程中会 unwinding call stack 并直接返回。Call stack 由 **activation records** 组成，其中每个 record 都是一个函数调用。Exceptions 传播的过程就是 activation records 从栈中弹出的过程。在 `error` 向上传播的过程中可以用 `error handler` 来捕获异常。此时的 exceptions 在传播时，会不断弹出 call stack 中的 activation records，直到遇到最近的 error handler，然后执行 handler。

这里用 \\(\operatorname{\mathtt{try}}\ t\_1\ \operatorname{\mathtt{with}}\ t\_2\\) 来表示 error handler，一旦遇到 `error` 就执行 \\(t\_2\\)。显然 \\(t\_1\\) 和 \\(t\_2\\) 的类型必须相同。


## Exceptions Carrying Values {#exceptions-carrying-values}

{{< figure src="/img/in-post/post-tapl/14-3-exceptions-carrying-values.png" caption="<span class=\"figure-number\">Figure 3: </span>Exceptions carrying values" >}}

发生异常时可以携带一些信息，包括异常类型等。这里用 \\(\operatorname{\mathtt{raise}} \operatorname{\mathtt{t}}\\) 来代替普通的 `error` 引发异常，其中 `raise` 可以当作一个 constructor，\\(t : T\_{exn}\\) 是其携带的信息，\\(\operatorname{\mathtt{raise}} \operatorname{\mathtt{t}} : T\\) 的类型类似于 `error`，便于嵌入表达式的任何位置。

引发异常后可以用 \\(\operatorname{\mathtt{try}}\ \operatorname{\mathtt{with}}\\)（`E-TryRaise`）语句来处理异常。`E-RaiseRaise` 用于处理嵌套的异常。`E-TryV` 则表明没有发生异常。

所携带的信息 \\(T\_{exn}\\) 可以有很多情况：

1.  `Nat`，即作为 `errno` 错误号，但是需要查表得到错误信息
2.  `String`，即错误相关的信息，但是需要进行 parse
3.  `variant type`，其中每种 `case` 还能携带额外的信息，但是只能抛出事先规定的几种异常
4.  `extensible variant type`（ML 的做法），可以使用 `exception l of T` 实时扩展异常类型 `exn`，使得 \\(T\_{exn}\langle l\_1 : T\_1 \dots l\_n : t\_n, l : T \rangle\\)：

    \\[
       \operatorname{\mathtt{raise}}\ l(t) \overset{\text{def}}{=} \operatorname{\mathtt{raise}}\ (\langle l = t \rangle\ \operatorname{\mathtt{as}}\ T\_{exn})
       \\]

    \begin{aligned}
    \operatorname{\mathtt{raise}}\ t\ \operatorname{\mathtt{with}}\ l(x) \overset{\text{def}}{=} &\operatorname{\mathtt{try}}\ t\ \operatorname{\mathtt{with}} \\\\
    &\quad \lambda e : T\_{exn}. \operatorname{\mathtt{case}}\ e\ \operatorname{\mathtt{of}} \\\\
    &\qquad\ \langle l = x \rangle \Rightarrow h \\\\
    &\qquad \vert\ \\\_ \Rightarrow \operatorname{\mathtt{raise}}\ e
    \end{aligned}

5.  Java 使用 `class` 来表示异常，其中异常相关的类需要继承自 `Throwable`。因此 Java 的异常类之间可以有继承关系（而 ML 中的异常都是平级的）。并且在 Java 中还区分了 `Exceptions` 和 `Errors`，前者可以被捕获处理，而后者会终止程序。Java 的另一个特殊点在于它是 **checked exceptions**，即方法抛出的异常是方法签名的一部分，并且方法调用者必须要处理方法中的所有异常。


## Exceptions as a control flow {#exceptions-as-a-control-flow}

Exceptions 不仅仅是一种错误处理机制，同时还代表了一种控制流结构：

-   A way to quickly escape from the computation
-   Handler
-   Value-carrying
-   A single type \\(T\_{exn}\\) shared all exception handler

在 OCaml 中，exceptions 不仅仅用于异常处理，还被用作控制程序的执行。


### Continuations {#continuations}

类似 exceptions，continuations 也可以用这样的方法建立类型。
