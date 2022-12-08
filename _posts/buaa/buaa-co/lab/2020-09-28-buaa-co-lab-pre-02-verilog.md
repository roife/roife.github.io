---
layout: "post"
title: "「BUAA-CO-Lab」 Pre-02 Verilog"
subtitle: "Verilog 电路建模"
author: "roife"
date: 2020-09-28

tags: ["北航计算机组成实验@课程相关", "课程相关@Tags", "体系结构@Tags", "集成电路@Tags", "Verilog@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 概述

Verilog 中可以用多种建模方式，这里关注结构级建模以及行为级建模。

行为级更关注电路的行为，可以用一些不可综合的语句，比如延时等，用类似于普通编程语言一样的语法描述出这个模块的行为。结构级建模就像用逻辑门画电路一样，设计出来的电路可综合。当行为级的仿真验证通过，则可以重新设计成结构级的电路。

```verilog
module Adder(
    input a,
    input b,
    input cin,
    output sum,
    output overflow
    );
    wire s1, s2, s3;
    //xor 与 and 均为原语，是系统预定义的模块
    xor xor1(sum, a, b, cin);
    and and1(s1, a, b);
    and and2(s2, a, cin);
    and and3(s3, b, cin);
    or or1(overflow, s1, s2, s3);
endmodule
```

需要注意的是，RTL 级也是行为级的一部分。但是 RTL 级一般都是指可综合的行为级表示。

# 组合逻辑

组合电路可以用 `assign`（配合三目运算符）或者 `always@(*) + =` 实现。

## 模板定义

模板定义有两种方法

```verilog
module AndGate(
    input i1,
    input i2,
    output o
    );
    assign o = i1 & i2;
endmodule
```

```verilog
module AndGate(i1, i2, o);
    input i1, i2;
    output o;

    assign o = i1 & i2;
endmodule
```

模块中所有操作都是并行进行的，因此不分先后顺序。

## 端口设置

格式为 `input/output [MSB, LSB] name`。

```verilog
input [3:0] a // 一个 4 位的总线
```

- `[3:0]`: little-endian，最高到最低位分别为 `a[3]~a[0]`
- `[4:1]`: little-endian，最高到最低位分别为 `a[4]~a[1]`
- `[0:3]`: big-endian，最高到最低位分别为 `a[0]~a[3]`

输出可以定义为 `output reg [3:0] a`，将其当作寄存器使用（等价于分开定义再驱动）。

## 数据类型

### wire 型

wire 类似于导线，不能存储数据，起到连接输入输出的作用，而且输入随着输出时刻改变，通常用于表示组合逻辑信号。

wire 一般使用 `assign` 驱动。

如果使用了未定义的变量，那么会被默认定义为 1 位 wire 类型。

```verilog
wire [31:0] a;
```

### reg 型

reg 型是寄存器，具有存储功能，一般在 `always` 块中使用。

reg 不能用 `assign` 赋值，并且不一定被综合成寄存器，可以用来建模组合逻辑。

reg 初始值默认为 `x`，可以存负数，但是表达式中默认被当作正数（可以用 `$signed(r)` 当成负数运算）。

```verilog
reg [31:0] mem [0:1023];
```

前面的中括号表示位宽，后面的中括号表示存储器数量，可以用 `mem[2]` 访问对应的寄存器。Verilog 中没有多维数组。

- `mem[0][7:0]`
  : 访问 `mem` 中 0 号寄存器的 `7:0` 位值
- `[bit+: width]`
  : 从起始 bit 位开始递增，位宽为 width
- `[bit-: width]`
  : 从起始 bit 位开始递减，位宽为 width

### 数字字面量

数字字面量格式为 `<位宽>'<进制><值>`，如 `10'd100`。

省略位宽时采用默认位宽（32bit），省略进制时默认采用十进制，如 `10 == 32'b1010`。

变量的位可以使用 `x` 和 `z`。`x` 为不定值，`z`（也可以写成 `?`）为高阻态。如 `4'b10x0`、`8'h4?`。

对于负数，负号要写在字面量整体前，如 `-8'd5`。

值之间可以用下划线提高可读性，如 `8'b0011_1010`，不可以放在进制和值之间。

字符串可以表示为数字字面量，如 `"AB" == 16'h4142`。存入寄存器时，字符串被存放在低位，同时高位用 `0` 填充。

### integer 型

默认为 32bit 有符号数，主要用于 for 循环。

### 符号数

wire，reg 默认为无符号数，可以用 `$signed()` 转换为有符号数。

但是如果表达式中同时存在符号数和无符号数，符号数会默认转换为无符号数，如 `a > $signed(b)` 等价于 `a > b`（`$signed()` 失效）。

对于移位运算符，其右侧的操作数总是被视为无符号数，并且不会对运算结果的符号产生影响。

### parameter 型

parameter 型类似于常量，必须要在编译时确定，但是它可以在实例化时被修改。parameter 可以用 `parameter 标识符 = 表达式；` 定义。

实例化时，如果需要修改 parameter，则必须用 `#()` 或者 `defparam [<hier.>] <param> = <const_expr>;`。

```verilog
module adder#(parameter width = 1, ...)(input a, ...);
  // ...
endmodule

// 也可以写成
module adder();
    parameter width = 1;
endmodule

// 实例化时指定
adder #(.width(8)) adder1(...);

// 或者用 defparam
defparam adder1.width = 8;
adder adder1(...);
```

此外，还可以用 `localparam` 来定义常量，避免实例化时被修改。

## 常用语法

### assign

`assign` 表示驱动信号，格式为 `assign a = b`，其中 `a` 为 wire 类型（要保证 `b` 也已经被驱动）。

因为 `assign` 会被实现为电路连接，因此不能用 `assign a = a + 1`，也不能在 `initial` 和 `always` 中使用。但是可以使用三目运算符。

### 运算符

Verilog 运算符与 C 相同，可以带 `x` 和 `z` 运算，但是没有 `++` 和 `--`。

此外，Verilog 有一些特殊的运算符：
- 逻辑右移 `>>` 与算术右移 `>>>`: 前者在最高位补 `0`，而后者在最高位补符号位
- `==` 与 `===`，`!=` 与 `!==`: 前者结果可能为 `x`，后者结果为确定的 `0` 或 `1`（`x` 与 `z` 也参加比较）
- 位拼接运算符 `{}`: 将几个位拼起来成为一个数字，如 `{a, b[3:0], w, 3'b101}`, `{b, {3{a, b}}} == {b, a, b, a, b, a, b}`
- 缩减运算符：单目前缀位运算，表示对每一位进行相同操作，如 `&B` 表示把每一位与起来
- 阻塞赋值 `=` 与非阻塞赋值 `<=`: 常用于 `always` 和 `initial` 块，在描述时序逻辑时要使用非阻塞式赋值

### 条件语句

当所有可能情况都被考虑（包括 `x` 和 `z`），则 `case` 语句会生成一个组合逻辑，否则会生成时序逻辑。

如果不写 `default` 或者 `else` 可能会导致电路生成锁存器（因为变量要保持原值）。

#### if

```verilog
if (a > b) begin
    out = a;
end
else begin
    out = b;
end
```

#### case

`case` 可以自动 `break`（和 C 不一样），并且 `case` 会进行 `===` 比较（`casex` 默认忽略 `x` 与 `z` 的比较，`casez` 默认忽略 `z` 位的比较）。

```verilog
case(data)
    0: out <= 4;
    1: out <= 5;
    2: out <= 2;
    3: begin
        out <= 1;
    end
    default: ;
endcase
```

### 函数与任务

#### function

函数格式如下：

``` verilog
function (<返回值的类型或范围>) 函数名；
    端口说明；
    变量类型说明；
    begin

    end
endfunction
```

如：

```verilog
function signed [1:0] ADD;
    input A, B, CIN;
    reg S, COUT;
    begin
        S = A ^ B ^ CIN;
        COUT = (A&B) | (A&CIN) | (B&CIN);
        ADD = {COUT, S};
    end
endfunction
```

函数返回值在函数内部是一个同名的寄存器，用 `<function name> = xxx` 可以赋值。返回值是一位的。

函数中不能包含 `#`、`@`、`wait`、`always` 等时间相关的语句，也不能调用 tasks（即不能调用消耗了时间的语句）。

函数至少有一个输入，必须有输出。

#### task

任务类似于 Pascal 中的 procedure，可以定义自己的仿真时间单位，也可以没有输入。

任务可以定义其他任务。

任务定义格式如下

```verilog
task <任务名>;
    <端口和数据类型声明>;
    begin
        <语句>;
    end
endtask
```

如：

```verilog
task light;
    output color;
    input [31:0] tics;
    begin
        repeat(tics)
            @(posedge clock);
        color = off;
    end
endtask
```

# 时序逻辑语法

## always 块

- 若 `always` 之后紧跟 `@(...)`，表示当**括号中的条件满足**时，将会执行 `always`，用于**时序逻辑**（`posedge` 表示上升沿，`negedge` 表示下降沿，默认为都敏感，多个条件用 `,` 或 `or` 隔开，当一个触发时就执行）
- 若 `always` 之后紧跟 `@*` 或`@(*)`，表示当**紧跟语句中信号变化**时，将会执行 `always`，一般与 reg 型和阻塞赋值配合使用，用于**组合逻辑**
- 若 `always` 之后紧跟语句，表示当反复执行，一般用来产生周期信号

```verilog
always @(posedge clk) // clk 到达上升沿触发
always @(a)

always @(*)

always #10
```

两个 `always` 语句如果同时触发就会产生竞争，触发的先后顺序不确定。

并且多个 `always` 语句间是并行执行的。

## initial 块

`initial` 一般用来初始化 reg 型，是不可综合的！

```verilog
initial begin
    mem = 0;
end
```

如果有多个 `initial` 块，那么这些  `initial` 块会并行执行。

## `final` 块

`final` 块在仿真结束时（`$finish`）执行。

## 基本语句

### 循环

#### repeat

格式为 `repeat(constant_num)`，括号内为常量表达式，用来重复数次操作。

```verilog
parameter size = 8;
repeat(size) begin

end
```

#### for

一般会定义一个 integer 作为循环变量。

```verilog
for (i=0; i<7; i=i+1) begin

end
```

#### while

```verilog
while () begin

end
```

## 时间控制

`#时间` 表示延时一段时间，可以用来产生时间信号。多条延时语句按顺序执行。

```verilog
always #5 clk = ~clk; // 产生周期为 10 的时钟信号
assign #5 b = a;      // 延时 5 个时间单位后赋给 b
#5 b = a;             // 延迟 5 个时间单位后执行赋值语句
```

```verilog
#5 a = 5        // [5] a = 5
#10 b = 10      // [15] b = 10
```

`@（时序条件）` 表示等待时序条件（如 `posedge` 等）满足。

## 块语句

### begin...end

`begin...end` 块用来表示顺序执行的语句，其中每条语句的延迟时间表示针对于上一条语句的延迟，执行完所有语句后跳出块。

```verilog
begin
    areg = breg;
    #10 creg = areg; // 上一个语句执行完 10 个单位时间后执行
end
```

### fork...join

`fork...join` 块用来表示并行执行的语句，其中每条语句的延迟时间表示针对进入块的时间，执行完所有语句或者遇到 `disable` 后跳出块。

因此在 `fork...join` 中，语句先后顺序无所谓。

```verilog
fork
    # 50 r = 'h35;
    # 100 r = 'hE2; // 上一条语句执行完 50 个单位时间后执行
join
```

### 命名块与 disable

可以给块命名，并且用 `disable` 跳出对应的块（类似于 `break`），可以理解为直接从标号对应的 `end` 块处跳出。

```verilog
begin : block1
    // ...
    disable block1;
end
```

### generate

`generate..endgenerate` 可以用来生成一些重复的语句。

#### generate-for

generate-for 必须用 `genvar` 定义的变量作为循环变量，必须用 `begin...end` 包裹语句且定义命名块。

命名块的名字可以用来对 generate-for 语句中的变量进行层次化引用。

```verilog
genvar i; // 可以定义到 generate 语句里面
generate
    for(i=0;i<SIZE;i=i+1)
        begin:bit
            assign bin[i]=^gray[SIZE-1:i];
        end
endgenerate

// 等同于
assign bin[0]=^gray[SIZE-1:0];
// ...
assign bin[7]=^gray[SIZE-1:7];
```

```verilog
generate
       genvar i;
       for(i=0;i<SIZE;i=i+1)
       begin:shifter
              always@(posedge clk)
                     shifter[i]<=(i==0)?din:shifter[i-1];
       end
endgenerate

// 等价于
always@(posedge clk)
       shifter[0]<=din;
always@(posedge clk)
       shifter[1]<=shifter[0];
// ...
```

#### generate-if

和 generate-for 类似，注意判断条件必须是常量。

```verilog
generate
   if(KSiZE == 3)
      begin: MAP16
       //针对尺寸为 3 的算法进行处理
     end
```

#### generate-case

```verilog
generate
     case (WIDE)
        9:
                  assign  d   =  a | b | c;
        12:       assgin  d   =  a & b & c;
        default:  assgin  d   =  a & b | c;
     endcase
endgenerate
```

## 寄存器

可复位的寄存器分为同步复位寄存器和异步复位寄存器。

```verilog
module flopr(input clk
             input reset,
             input [3:0] d,
             output [3:0] q);
    // asynchronous reset
    always @(posedge clk, posedge reset)
        if (reset) q<= 4'b0;
        else q <= d;
endmodule

module flopr(input clk
             input reset,
             input [3:0] d,
             output [3:0] q);
    // synchronous reset
    always @(posedge clk)
        if (reset) q<= 4'b0;
        else q <= d;
endmodule

// 使能复位寄存器
module flopr(input clk
             input reset,
             input en,
             input [3:0] d,
             output [3:0] q);
    // synchronous reset
    always @(posedge clk)
        if (reset) q<= 4'b0;
        else if(en) q <= d;
endmodule
```

# Verilog 层次化事件队列

Verilog 中的事件从高到低可以分为四个队列，只有优先级高的队列完成后才进行下一个队列。

非阻塞赋值被拆分为两个事件（等号左边为 LHS，等号右边为 RHS）

1. 动态事件队列（阻塞赋值，计算 RHS，连续赋值 `assign`，`$display`)
2. 停止运行的时间队列 `#0`（不推荐使用）
3. 非阻塞事件队列（更新 LHS）
4. 监控事件队列（`$monitor` 等命令）

其中同一个队列的执行顺序按照在 `begin...end` 块中的顺序执行，RHS 也按照语句事件计算。

# 阻塞赋值和非阻塞赋值

- 阻塞赋值 `=`: 顺序执行（和 C 一样），不允许其他语句干扰，如果两个阻塞赋值同时触发，那么执行顺序是不确定的
- 非阻塞赋值 `<=`: 块结束后才开始赋值（并行）

```verilog
a <= 1'b1;
b <= 1'b0;
b <= a;
c <= b;
// b == 1'b1, c == 1'b0
```

- 非阻塞赋值一般和 `always @(posedge xxx)` 结合使用生成时序逻辑和寄存器电路
- 连续复制和 `assign` 结合使用生成组合逻辑
- 阻塞赋值和 `always @(*)` 结合使用
- 阻塞赋值和非阻塞赋值不能在同一个 `always` 块中使用，如果同时存在应该都改为非阻塞赋值

在组合逻辑（`always @(*)`）中使用非阻塞会造成自触发 always 块。

## 自触发 always 块

一般在 `always` 语句中不允许对自己进行触发。
如果使用阻塞赋值不会触发事件，但是非阻塞赋值会触发。（都是不推荐的写法）

```verilog
always @(clk) #10 clk = ~clk; // 延时后赋值仍在块内，所以不会触发
always @(clk) #10 clk <= ~clk; // 延时后赋值，此时已经跳出 always 块了，所以会造成自触发
```

# 结构化建模

将电路分为多个模块（module），然后在其他电路中调用并连接输入输出可以简化代码。

```verilog
module mux4(input [3:0] d0, d1, d2, d3,
            input [1:0] s,
            output [3:0] y
            );

            reg [3:0] low, high;

            mux2 lowmux(d0, d1, s[0], low);
            mux2 highmux(d2, d3, s[0], high);
            mux2 finalmux(low, high, s[1], y);
endmodule
```
![结构化建模](/img/in-post/post-buaa-co/mux4-structural-modeling.png "structural-modeling"){:height="600px" width="600px"}

# 高级语法

## 模块实例化

```verilog
module Sample (
    input a,
    input b,
    input reset,
    output c
    );

// 其他模块
Sample uut1(x, y, z);
Sample uut2(.b(y), .a(x), .c(z)); // 两种方法不能混合使用
```

## 预处理与宏

编译预处理命令以符号 `` ` `` 开头。

宏定义为 `` `define 标识符（宏名）字符串（宏内容）``，使用时标识符前也要加上 `` ` ``。

```verilog
`define WORDSIZE 8

reg[1:`WORDSIZE] data;
// 相当于定义 reg[1:8] data;
```

用 `` `default_nettype type `` 可以设置缺省类型，若代码中有两个以上的 `` `default_nettype`` 宏，则将会以最后一条为准。一般用 `` `default_nettype none`` 禁止缺省类型。

用 `` `timescale[时间单位]/[时间精度] `` 可以定义仿真的时间尺度。如 `` `timescale 1ns/1ps; `` 表示时间为 `1ns` 的整数倍，延迟的精度可达到 `1ps`。

类似 C 语言，还有 `` `include "文件名" ``、`` `ifdef ``、`` `else ``、`` `elsif ``、`` `endif ``、`` `ifndef `` 等预处理语句。

## 系统任务

系统任务类似于库函数。

### \$display

类似于 `printf`，用来输出信息。

```verilog
$display("a = %d,b = %d\n",a,b);
```

### \$monitor

格式为 `$monitor(p1,p2,…,pn);`，如 `$monitor($time,,"a= %b",a_monitor);`（`,,` 表示空参数，显示为空格）。
当监控的数据发生变化时则输出数据或表达式。

`$monitor` 可以在 initial 块中调用（`$display()` 不可以）。

```verilog
$monitor("x=%b,y=%b,cin=%b",x,y,cin);
```

可以用 `$monitoron;` 和 `$monitoroff;` 进行开关，打开时会自动输出一次现在的值。
如果同一时刻多个值发生了变化，只会执行一个 `$monitor`（因此要及时关闭）。

### \$readmemh

类似于 `fread()`，用于读入十六进制。

格式有三种：
- `$readmemh(“<数据文件名>”,<存储器名>);`
- `$readmemh(“<数据文件名>”,<存储器名>,<起始地址>);`
- `$readmemh(“<数据文件名>”,<存储器名>,<起始地址>,<结束地址>);`

文件中的内容必须是十六进制数字 `0~f` 或是不定值 `x`，高阻值 `z`，不同的数用空格或换行隔开。

假如数字的位数大于数组元素的位数，那么只有低位会被读入，剩下的高位会被忽略。

类似还有 `$readmemb()`。

# FSM

Verilog 在 FSM 中主要作用于代码编写部分。

FSM 一般用 `` `define `` 和 `case` 来实现，由组合逻辑和时序逻辑两部分组成。
其中组合逻辑可以用 `assign`，也可以用 `always @(*) + =`。

```verilog
`define S0 2'b00
`define S1 2'b01
`define S2 2'b10
`define S3 2'b11

always @(posedge clk)
begin
    case(status)
    `S0 : begin
                if (num == 2'b01) status <= `S1;
                else if (num == 2'b10) status <= `S0;
                else if (num == 2'b11) status <= `S0;
                else status <= `S0;
            end
    `S1 : // ...
    `S2 : // ...
    `S3 : // ...
    endcase
end

assign ans = (status == `S3) ? 1'b1 : 1'b0;
```

Moore 型的输出只和状态有关，Mealy 的输出和输入也有关。

```verilog
assign zo = (state==`S4); // Moore
assign zo = (state==`S3) & (data==1'b0); // Mealy
```

# Verilog 工程开发方法

- 需求分析：包括 `端口定义`（表格）、`组合逻辑设计`、`时序逻辑`
- 需求实现：注意代码风格
- 仿真与调试：使用 testbench 和 ISim
- 综合工程：可综合的工程要满足一系列要求
  + 不使用 `initial`、`fork`、`join`、`casex`、`casez`，延时语句（如 `#10`），系统任务（如 `$display`）等语句
  + 用 `always` 过程块描述**组合逻辑**时，应在敏感信号列表中列出所有的输入信号（或用星号 `@(*)`
  + 用 `always` 过程块描述时序逻辑时，敏感信号只能为时钟信号
  + 所有的内部寄存器都应该能够被复位
  + 不能在一个以上的 `always` 过程块中对同一个变量赋值。而对同一个赋值对象不能既使用阻塞式赋值，又使用非阻塞式赋值
  + 尽量避免出现锁存器，例如，在 `if` 或 `case` 的所有条件分支中都对变量明确地赋值
  + 避免混合使用上升沿和下降沿触发的触发器

# Testbench

Testbench 本质上是一个用于测试的 module。

生成 testbench: 右键单击 `Design` → `New Source` → `Verilog Test Fixture` → 选择模块。

```verilog
module io;
    // Inputs
    reg clk;
    reg [7:0] char;

    // Outputs
    wire [1:0] format_type;

    // Instantiate the Unit Under Test (UUT)
    cpu_checker uut (
        .clk(clk),
        .char(char),
        .format_type(format_type),
    );

    initial begin
        // Initialize Inputs
        clk = 0;
        char = 0;

        // Wait 100 ns for global reset to finish
        #100;

        // Add stimulus here
        #10;
        char = "^";
        #10;
        char = "1";
    end

    always #5 clk=~clk; // 控制时钟周期为 10

endmodule
```

# 杂项

## 常见错误

- 波形出现不定值 `x`: reg 型没有初始值
- 波形出现高阻 `z`: 电路存在没有连线的变量信号（wire 型）

## iverilog

- 编译文件：`iverilog [.v] [.v] -o [.out]`
- 运行文件：`vvp [.out]`

查看波形可以用 `gtkwave`。

## 电路设计相关概念

- IP 核的种类
  - 软核：功能经过验证、可综合的的较大规模 Verilog 模型
  - 固核：功能经过验证、在 FPGA 上实现的较大规模 Verilog 模型
  - 硬核：功能经过验证、在 ASIC 上实现的较大规模 Verilog 模型
- 自顶向下的设计流程
  - 首先将整个系统分解为若干个子系统，并对其在行为级上进行仿真
  - 然后针对每个子模块进行设计（设计成可综合的电路，或者拆分成更小的模块用行为级验证并重复这个步骤）

# 参考资料

1. *Digital Design and Computer Architecture 2nd*, Chapter 4
2. *Verilog 数字系统设计教程（第四版）*
