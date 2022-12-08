---
layout: "post"
title: "「System Verilog」 03 声明空间与子程序"
subtitle: "Function 与 Task"
author: "roife"
date: 2022-10-16

tags: ["System Verilog@编程语言", "集成电路@Tags", "SV for Verification@读书笔记"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 声明空间

## 包

SV 中在 `module` 之上引入了 `package` 的概念。包可以 `import` 其他包，并且定义类型、常量、`module`、全局 `task`/`function` 等。

```verilog
package pkg;
    // ...
endpackage
```

可以用 `::` 来引用包的内容，例如 `pkg::a`。

## `import`

可以用 `import` 来引入包内的名字，并且可以使用通配符 `*` 来引入所有名字（没有使用的名字不会引入，只会引入使用了的名字）。

```verilog
import default_pkg::opcode_t::ADD;
// ...

// 通配符
import definitions::opcode_t::*;
```

## 作用域

SV 引入了类似于 C++ 的编译单元的概念，可以用 `$unit` 来指代当前编译单元作用域，处于 `package` 和 `module` 之外（但是每个编译器对于编译单元的定义可能不同，可能是单一文件，也可能是所有文件，取决于一次编译多少文件）。

此外，可以用 `$root` 来指代顶层作用域。需要引用其他文件的元素时，可以用类似于 `$root.top.clk` 的语法。

## 程序块

在 SV 中，为了能够区分开设计和验证，引入了“程序块”的概念。所有的测试代码都写在 `program` 中。程序块内不能嵌套包含。

```verilog
program test(arb.TEST arbif);
    initial begin
        // ...
    end
endprogram
```

## 简化 `begin...end`

在 SV 中，不再要求在 `function` 和 `task` 中再包含 `begin...end`。

```verilog
task t;
    // ...
endtask
```

# 返回值改进

## `void function`

在 Verilog 中，`function` 不能消耗时间（不能延时，不能调用 `task`）；必须有返回值，而且返回值必须被使用

因此 SV 中允许 `void function` 来让 `function` 不返回任何值，可以在里面实现一些调试语句。

```verilog
function void print_state(...);
    $displat("...");
endfunction
```

对于有返回值的函数希望忽略返回值，可以用强制类型转换：

```verilog
void' (func());
```

## `return`

SV 中新增了 `return` 语句，可以在 `task` 或者 `function` 中使用。

# 子程序参数

## 函数的 `output` 参数

SV 中允许在 `function` 中使用 `output` 参数：

```verilog
function [63:0] add (input [63:0] a, b,
                     output overflow);
    {overflow, add} = a + b;
endfunction
```

可以达到多返回值的效果（注意仍然需要有返回值）。

## 声明

在 SV 中，允许用 C 风格的参数声明方式：

```verilog
// Verilog 中的方式
task t;
    output [31:0] x;
    reg    [31:0] x;
    // ...
endtask

// SV 中的方式
task t(output logic[31:0] x,
       input  logic y);
   // ...
endtask
```

参数方向和 Verilog 一样，有 `input`/`output`/`inout`（后面两个只能在 `task` 中使用）。

这里直接使用 `logic`，就不用再区分 `reg` 和普通的线网类型了。

同时，在 SV 中还可以进一步简化**方向**和**类型**，写成 `task t(y, output [31:0] x)`，但是可能会导致一些 bug，因此还是推荐写明所有参数的方向和类型。

## 引用参数

普通的传参只能通过复制传递标量，而指定 `ref` 之后可以传递一个存储器的引用。

```verilog
function void print (const ref bit [31:0] a[]);
    // ...
endfunction
```

此外，使用 `ref` 还可以暴露内部对于引用数据的修改，而不用等到整个 task 结束再触发相应任务。

```verilog
task bus_read(ref logic [31:0] data);
    // ...
    @(posedge bus.enable) data = bus.data;
    // ...
endtask

initital
    fork
        bus_read(addr, data);
        thread2: begin
            @data;             // 当 data = bus.data 触发时立即触发，而不用等待整个 task 返回
    end
end
```

## 默认参数

类似 C 语言，而且允许中间的值被省略。

```verilog
function void print_checksum(ref bit [31:0] a[],
                             input bit [31:0] low = 0
                             input int high = -1);
    // ...
endfunction

print_checksum(a, 1);
print_checksum(a, , 2);
```

## 命名参数

和  Verilog 中的一样。

```verilog
task many(input int a = 1, b = 2, c = 3, d = 4);
endtask

many(.c(5));
```

# `disable`

可以用 `disable` 关键字来取消 `task` 中的特定块。

```verilog
initial display();

initial #50 disable display.T_DISPLAY();

task display;
    begin: T_DISPLAY
        $display("[%0t] T started", $time);
        #100;
        $display("[%0t] T ended", $time);
    end

    begin: S_DISPLAY
        #10;
        $display("[%0t] S started", $time);
        #20;
        $display("[%0t] S ended", $time);
    end
endtask

// xcelium> run
// [0] T_Task started
// [60] S_Task started
// [80] S_Task ended
```

# `always`

SV 中明确区分了 `always` 在不同场合下的用途。

## `always_comb`

`always_comb` 用于组合逻辑，类似于 `always @(*)`，但是明确是组合电路，所以不会搞出 latch。编译器会自动推断出需要的敏感值列表。

```verilog
always_comb
    if (a == 1'b1) b = 1'b1;
    else b = 1'b0;
```

需要注意的是，`always_comb` 在模拟的零时刻会自动执行一次。

## `always_ff`

`always_ff` 用于时序逻辑，类似于 `always @(posedge clk)`，用于建模 flip-flop 触发器。

```verilog
always_ff @(posedge clock, negedge resetN)
    if (!resetN) q <= 0;
    else q <= d;
```

## `always_latch`

`always_latch` 同 `always_comb`，会自动推断敏感值列表，专门用于建模 latch。

```verilog
always_latch begin
    if (!resetN) enable <= 0;
    else if (ready) enable <= 1;
    else if (overflow) enable <= 0;
end
```
