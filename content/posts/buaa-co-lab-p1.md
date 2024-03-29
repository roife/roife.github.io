+++
title = "[BUAA-CO-Lab] P1 Verilog 模块及状态机"
author = ["roife"]
date = 2020-10-31
aliases = ["/posts/2020-10-31-buaa-co-lab-p1"]
series = ["buaa-co"]
tags = ["体系结构", "verilog"]
draft = false
+++

## 上机总结 {#上机总结}

第一题是对输入数字计算出 1 的数量，并进行加权求和。

第二题是个迷惑的时序电路应用题，煎饼的过程有四个状态切换，在特定的状态可以进行翻面操作，答案要在可以翻面的时候翻面，并且输出当前的煎饼状态。

第三题是个字符串识别（日期格式合法性判断），和课下差不多，没什么好说的。

第一题感觉不是很签到的样子，需要用 `always @(*)` 加上 `for` 循环写组合电路，注意组合电路要和阻塞赋值配合。第二题是一只很让人讨厌的应用题，关键是要猜到出题人的想法。第三题还算简单，状态和转移都不复杂。

总之感觉不是很难，但是时序电路应用题是真的讨厌，所以虽然考试延长了半个小时，但是通过率依旧不乐观。 考场上大概四十分钟能写完 1，3 两题，然后第二题卡个一小时（溜）。

然后就是问答环节被问倒了（悲），回去一定好好看 ISE 用法。

总结：

1.  平时很少遇到 `always @(*)` 写组合电路的用法，需要注意
2.  遇到应用题不要慌，多猜猜出题人的想法


## 课下总结 {#课下总结}


### `$signed()` {#signed}

这里写一下关于 `$signed()` 的理解。

`$signed()` 的真正功能是决定数据如何进行补位。一个表达式（特别注意三目运算符）中如果存在一个无符号数，那么整个表达式都会被当作无符号数。


#### signedness {#signedness}

-   `self-determined expression`：指一个位宽可以由该表达式本身独立决定的 expression
-   `context-determined expression`：指一个位宽由其本身以及其所属的表达式共同决定的 expression（例如一个阻塞赋值语句右侧表达式的位宽同时受左右两侧位宽的影响）

Verilog 在计算表达式前，会先计算表达式的 signedness。计算方式如下：

-   仅由操作数决定，不由左侧决定（如 `assign D = exp`，`exp` 符号与 `D` 无关。这一点区别于位宽，位宽由左右两侧所有表达式的最大位宽决定）
-   小数是有符号的，显式声明了进制的数无符号，除非用修饰符 s 声明了其有符号（如 `'d12` 无符号，`'sd12` 有符号
-   位选_多位选择_位拼接的结果无符号（如 `b[2]`、`b[3:4]`、`{b}` 均无符号，这也是隔壁 bit extender 有同学用三目运算符结果 WA 了的原因）
-   比较表达式的结果无符号（要么是 `0`，要么是 `1`）
-   由实数强转成整型的表达式有符号
-   一个 self-determined expression 的符号性仅取决与其操作数
-   对于 context-determined expression，只有所有操作数均为有符号数时表达式才有符号

在计算表达式时，先由以上规则得出最外层表达式的符号性，再向表达式里的操作数递归传递符号性。

`$signed()` 函数的机制是计算传入的表达式，返回一个与原表达式的值和位宽完全相同的值，并将其符号性设为有符号。该函数可以屏蔽外部表达式的符号性传递。

另外就是算术右移运算符（`>>>`）的有操作数不影响结果的符号，所以没必要加上 `$signed()`。


#### 一些例子 {#一些例子}

下面是一些例子：

-   `assign C = (ALUOp==3'b101) ? $signed(A)>>>B : $signed(A+B);` 正确
-   `assign C = (ALUOp==3'b101) ? $signed(A)>>>B : A+B;` 错误
-   `assign C = (ALUOp==3'b101) ? $signed(A)>>>B : 0;` 正确（`0` 被看作有符号数）
-   `assign C = (ALUOp==3'b101) ? $signed(A)>>>B : 32'b0;` 错误（显式声明了进制，被当成无符号数）

特别的，还有：

-   `assign C = (ALUOp==3'b101) ? $signed(signed(A)>>>B) : $signed(A+B);` 正确

因为外层推导出是无符号，但是外面的 `$signed` 阻止了 unsignedness 向内层转移。


### 位扩展 {#位扩展}

`$signed()` 用法太玄妙了，不如直接用位扩展替代。

```verilog
{{16{imm[15]}}, imm} // 将 [15:0] 的 imm 扩展到 32 位
```


### testbench 的优雅写法 {#testbench-的优雅写法}

```verilog
reg [0:1023] S = "abcd";

initial begin
   while(!S[0:7]) S = S << 8;

   for(; S[0:7]; S = S << 8) begin
      in = S[0:7];
      #5;
   end
end
```


### 字符串识别状态机的方便写法 {#字符串识别状态机的方便写法}

识别 `begin` 和 `end` 配对的状态机。

```verilog
module BlockChecker (
                     input       clk,
                     input       reset,
                     input [7:0] in,
                     output      result
                     );

   reg [31:0]                    cnt;
   reg                           valid;
   reg [255:0]                   bfr; // 缓冲区

   initial begin
      cnt <= 0;
      valid <= 1'b1;
      bfr = "";
   end

   always @(posedge clk, posedge reset) begin
      if (reset) begin
         cnt <= 0;
         valid <= 1'b1;
         bfr = ""; // 每次复位一定要清除缓冲区
      end else begin
         bfr = (bfr << 8) | in | 8'h20;

         if (valid) begin
            if (bfr[47:0] == " begin") cnt <= cnt + 1;
            else if (bfr[55:8] == " begin" && bfr[7:0] != " ") cnt <= cnt - 1;
            else if (bfr[31:0] == " end") cnt <= cnt - 1;
            else if (bfr[39:8] == " end" && bfr[7:0] != " ") cnt <= cnt + 1;
            else if (bfr[39:8] == " end" && bfr[7:0] == " " && cnt[31]) valid <= 1'b0;
         end
      end
   end

   assign result = ((cnt == 0) && valid);

endmodule
```
