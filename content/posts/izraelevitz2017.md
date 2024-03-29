+++
title = "[ICCAD'17] Reusability is FIRRTL ground: Hardware construction languages, compiler frameworks, and transformations"
author = ["roife"]
date = 2022-11-06
series = ["paper-notes"]
tags = ["IR", "HDL", "ICCAD"]
draft = false
+++

> 这篇文章对硬件开发中“没有像软件那样发展出大量可重用的库”的现象进行分析。
>
> 基于此，作者强调了硬件构建语言（Hardware Construction Languages，HCL）和开源硬件编译框架（Hardware Compiler Framework，HCF）的重要性，并提出了 FIRRTL 来作为 HCF 的 IR


## Introduction {#introduction}


### Motivation {#motivation}

-   专用硬件下的软件表现比通用处理器好很多，这催生了对各类专用硬件的需求；但是不同的专用硬件产品会使用不同的专用 RTL，现有的硬件开发方法学在实际开发中遇到了困难
-   软件开发中，有大量可重用的开源库，极大地降低了软件开发和验证的成本，而硬件开发中却没有这样的可重用库

借此，作者提出了疑问：**"为什么硬件开发中没有这样的可重用库？"**


### Contribution {#contribution}

-   针对上述问题，作者提出并分析了两个猜想：
    1.  HDL 缺乏软件语言那样的表达力来开发可重用的库（如函数式、模块化等特性）
    2.  RTL 的定制化程度非常高，导致 RTL 的可重用性很低
-   分析了 HCL 在可重用库开发中的重要性，并提出了一套将 RTL 从开发限制中解放出来的开源 HCF 实现
-   在实现的 HCF 上评估了许多 transformations 的可用性


## Hypotheses {#hypotheses}

首先作者指出虽然目前有一些可重用的 IP 核，但是它们的专用程度很高，不足以成为运算单元这样基础的库。接着作者否定了对问题的两种猜想：

-   没有人尝试去推动这件事（很多公司做了但是失败了）；
-   缺少一个开源社区（软件库往往由少数人开发，但不妨碍它们被广泛使用）。


### HDL 缺乏表达力 {#hdl-缺乏表达力}

现在的 HDL 缺乏面向对象、多态、高阶函数等特性，无法实践抽象、封装、模块化的思想。这里作者举了两个例子：

-   在实现加法树时，无法用递归生成语句，需要设计者手动展开循环，导致类似的代码不能复用
-   设计一个 filter 模块时，不能使用高阶函数，需要在模块中硬编码条件

而现有的其他电路设计语言中：SV 缺乏 FP 的特性且标准过于复杂；High-level synthesis（HLS）则为了可综合性牺牲了源语言的表达力。

因此作者强调了 HCL 的重要性。在 HCL 中，硬件实体会被抽象为数据结构，并通过 **elaboration** 的过程导出到现有的 HDL 中。

Chisel 等 HCL 直接使用 RTL 抽象，将 HDL 的硬件原语与现有的编程语言相结合，在利用宿主语言提供了更强的表达力的同时，也不会产生额外的开销。这能让电路设计变得更加参数化和模块化，有利于代码的重用。


### 一些复杂因素制约了 RTL 设计 {#一些复杂因素制约了-rtl-设计}

在电路的综合时，一些复杂因素会影响硬件 RTL 的设计：

-   ASIC 实现 memory 时往往不用 Verilog 的寄存器数组，而是会用 fab 厂商提供的 SRAM，限制了代码重用
-   实现 FPGA 电路时会采用 FPGA 内硬编码的逻辑块来达到更好的性能和功耗，不利于代码重用

并且目前的商业的 CAD 工具以及开源工具（如 Yosys、PyVerilog、Verific）有着与 Verilog 绑定、IR 层级太低等问题，不足以进行 RTL-to-RTL 变换来解决上面的问题：

-   Yosys：开源 Verilog RTL 综合器，可以将 Verilog 转换到 ASIC standard cell lib 或 Xilinx FPGA 上，但不关注 RTL 变换
-   PyVerilog：聚焦于 Verilog 的开源 RTL-to-RTL 转换工具，不支持 SRAM 接口或聚合类型
-   Verific：商业 Verilog/VHDL 解析器，可以在 AST（但是要求支持源语言所有特性）或语言无关的线网格式上写 pass

因此作者提出模仿软件编译框架，由前端将 Chisel 或 Verilog 翻译成 FIRRTL，并在 FIRRTL 上面做优化，最后将结果用于仿真或综合。


## Solutions {#solutions}


### FIRRTL {#firrtl}


#### Overview {#overview}

FIRRTL 的设计过程中贯穿着三条准则：

-   **clear**：语法定义严格且直接
-   **simple**：IR 种类尽量少（方便下游工具进行综合仿真）
-   **rich**：尽可能多得捕获设计者的意图（FIRRTL 包含丰富的元素，包括内存结点、聚合类型、时钟类型等）

在语义上，FIRRTL 为封装性定义了 modules，为状态元件定义了寄存器和内存结构，为组合逻辑定义了原语操作和 mux。

FIRRTL 采用了三层结构（`high form`、`middle form`、`low form`），并且每一层都是前一层的子集。其中，FIRRTL 的 `low form` 可以直接对应到 Verilog 的结构。


#### In-Memory Representation {#in-memory-representation}

FIRRTL 在内存中用 **AST** 表示，transformations 可以通过 walk 的方式对 AST 进行遍历。如果需要全局信息，transformations 可以先 walk 一遍 AST，收集信息建出自定义的数据结构，然后再第二次遍历来对 AST 进行操作。

如果 transformations 需要基于其他数据结构来操作（比如组合逻辑的循环检测需要基于有向图），HCF 中也提供了用于构建相关数据结构的库。

FIRRTL 的 AST 中的所有结点都用对象表示，并且均继承自 `circuit`、`module`、`port`、`statement`、`expression`、`type` 其中之一。每个结点可以包含子结点，如下图：

{{< figure src="/img/in-post/post-paper-notes/izraelevitz2017-ast-nodes.png" caption="<span class=\"figure-number\">Figure 1: </span>AST nodes in FIRRTL" width="700" >}}

{{< figure src="/img/in-post/post-paper-notes/izraelevitz2017-ast-tree.png" caption="<span class=\"figure-number\">Figure 2: </span>AST tree in FIRRTL" width="700" >}}

在 FIRRTL 中，有 `Integer`、`Fixed-Point`、`Clock`、`Reset`、`Analog` 五种基本类型，并且有 `Vector`、`Bundle` 和 `Passive`（只能单向流动，可与其他类型一起用）类型。


#### Transformations {#transformations}

Transformations 可以指定接受某一级的 IR 作为输入，并指定输出 IR 的级别。每一个 transformation 结束后编译器都会对 IR 的形式进行检查，以确保对代码的变换是安全的。

Transformation 使用 `map` 函数来遍历 AST，每个下面是对端口进行变换的一个例子：

```scala
def onP(p: Port): Port = ...
val myMod = Module(..., Seq(port1, port2), stmt)
val m1 = myMod.map(onP)
// m1 is Module(..., Seq(onP(port1), onP(port2)), stmt)
```

此外，作者介绍了几种 Transformations：

-   Simplification Transformations：将高级 IR 转换到低级 IR，即分为 `high-to-mid` 与 `mid-to-low` 两种
-   Analysis Transformations：例如 Node-counting，early area estimations，module hierarchy depictions
-   Optimization Transformations：例如 Constant Propagation，CSE，DCE
-   Instrumentation Transformations：例如添加 hardware counters 和 hardware assertions
-   Specialization Transformations：针对不同的 ASIC 和 FPGA 对 RTL 进行修改


## Case Study: Custom Design on a new ASIC Process {#case-study-custom-design-on-a-new-asic-process}

作者在这部分基于 RocketChip 设计了一个芯片，并在 28nm 工艺下布局到 DRC/LVS-clean GDS。在整套流程中仅添加了 1817 行新代码，并且大部分代码用于验证工作和参数配置。

在开发过程中重用了前面提到的将内存结构转换为 SRAM 的 transformations。为了能够为 SRAM 提供额外的初始化和控制引脚，并按照综合器的要求独立指定每个模块的时钟域和电压域，作者写了额外的两个 pass，共 680 行新代码。

在整个过程中有 94% 的代码被重用。
