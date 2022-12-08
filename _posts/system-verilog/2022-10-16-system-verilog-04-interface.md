---
layout: "post"
title: "「System Verilog」 04 接口"
subtitle: "Function 与 Task"
author: "roife"
date: 2022-10-16

tags: ["System Verilog@编程语言", "集成电路@Tags", "SV for Verification@读书笔记"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 接口

在 Verilog 开发中，如果想要给一个底层模块增加信号，就要给它上面的各层模块都加上信号，并且要将对应的信号准确连接。在 SV 中，利用接口可以将若干相关的信号打包整合起来方便复用。并且在接口中也能实现函数、`task` 等内容。

语法为：

```verilog
interface [name]([port_list]);
    [list of signals]
endinterface
```

下面是一个例子：

```verilog
interface arb_if(input bit clk);
    logic [1:0] grant, req;
    logic rst;
endinterface
```

通常在接口中会使用 `logic` 类型，这样就可以同时支持用作 `wire` 和 `reg`。

需要注意的是，SV 中的接口和 OO 中的接口不同，SV 中的接口不是一个对类的约束，而是包含了若干信号的**模块**（更像是一个 struct）。因此接口作为参数时，默认是 `ref` 或者 `inout` 的。

下面是一个验证的例子。通过同一个接口可以方便地将 DUT 和 TB 在 Top 中连接起来。

```verilog
// DUT (Design Under Test)
module arb(arb_if arbif);
    always @(posedge arbif.clk) begin
        if (arbif.rst)arbif.grant <= 2'b00;
        else // ...
    end
endmodule

// Testbench
module test(arb_if arbif);
    initial begin
        @(arbif.clk);

        arbif.req <= 2'b11;
        $display("[%t] req = %b", $time, arbif.req);

        repeat (10) @(arbif.clk);
        if (arbif.grant != 2'b01) $display("[%t] ERROR: grant = %b", $time, arbif.grant);

        $finish;
    end
endmodule

// Top
module top;
    bit clk;
    always #5 clk = ~clk;

    arb_if arbif(.clk(clk));
    arb arb(.arbif(arbif));
    test test(.arbif(arbif));
endmodule
```

## 隐式端口连接

如果接口实例的名称和对应的端口名称相同，则可以直接用 `.*` 来连接。

```verilog
arb arb(.*);
```

# `modport`

原始的 `interface` 中只声明了变量，而不包括信号的方向（因为信号在不同的模块里方向不同）。此时可以使用 `modport` 来定义端口的方向。

```verilog
modport [identifier](input [port_list], output [port_list]);
```

下面是一个例子

```verilog
interface arb_if(input bit clk);
    logic [1:0] grant, req;
    logic rst;

    modport DUT(input clk, req, rst,
                output grant);
    modport TEST(input clk, grant,
                output req, rst);
    modport MONITOR(input clk, grant, req, rst);
endinterface
```

在使用时，可以在类型中直接使用 `interface.modport` 来指定方向。

```verilog
module arb(arb_if.DUT arbif);
    // ...
endmodule

// 也可以在实例化时指定
arb arb(.arbif(arb_if.DUT));
```

# 通用接口

即直接在端口声明中用 `interface` 来指明对应的端口是一个接口，而不是某个具体的接口。

```verilog
module myDesign(interface a, input logic clk);
    // ...
endmodule

module yourDesign (interface b, input logic clk);
    // ...
endmodule

module tb;
	logic clk = 0;

	myInterface  _if;
	myDesign 	md0 ( .*, .a(_if));
	yourDesign	yd0 ( .*, .b(_if));
endmodule
```

# `clocking` block

编写 TB 时可能会遇到一个问题，即“什么时候把接口的输出信号喂给 DUT，什么时候从 DUT 采样接口的输入信号进行分析”，二者在仿真时可能会导致竞争。因此 SV 引入了 `clocking` block 来解决这个问题。

一个接口块可以包含多个 `clocking` 块，每个块内只能有一个时钟表达式，对应着一个时钟域。在 `clocking` 块内，可以使用 `default` 指定默认时钟偏移，并分别指定每个信号相对于事件偏移（即输入信号在**事件前**多久被采样，输出信号在**事件后**多久被驱动）。

> 涉及到时钟块时，信号的采样和驱动都不是立即发生的，而是在时钟块内的时钟事件发生时才发生。

格式为：

```verilog
[default] clocking [identifier_name] @ [event_or_identifier]
	default input #[delay_or_edge] output #[delay_or_edge]
	[list of signals]
endclocking
```

如下面的例子：

```verilog
clocking ck1 @ (posedge clk);                   // 当 clk 在上升沿时触发
    default input #5ns output #2ns;             // 输入信号会在上升沿前的 5ns 被采样，输出信号会在上升沿 2ns 后被驱动

    input data, valid, ready = top.ele.ready;   // 上升沿前 5ns 采样
    output negedge grant;                       // grant 被重新设定为下降沿驱动

    input #1step addr;                          // addr 被重新设定为上升沿后第一步被采样
    input #1 output #3 sig;                     // inout 信号需要设定两个
endclocking
```

如果没有用 `default` 进行指定，则默认：
- 输入在事件的 `#1step` 被采样
- 输出在事件的 `#0` 后被驱动
- 注意：如果输入信号被设定为 `#0`，则会在事件发生时被采样（但是这可能会导致竞争，注意这和 `#1step` 不同）

定义了时钟块后，可以用 `@if.ck1` 来指定某个时钟块的触发事件，并用 `if.ck1.data` 在该时钟块规则下采样信号/驱动信号。

## 在 `modport` 中使用

可以直接在 `modport` 中使用时钟块：

```verilog
interface arb_if(input bit clk);
    bit grant, req, rst;

    clocking cb @(posedge clk);
        output req;
        input grant;
    endclocking

    modport TEST(clocking cb, output rst);
    modport DUT(input req, rst, output grant);
endinterface
```

此时如果用了 `TEST`，那么必须要 `arbif.cb.req`，而不能直接用 `arbif.req`。
