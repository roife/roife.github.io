---
layout: "post"
title: "「System Verilog」 02 控制流"
subtitle: "SV 中的控制流语句"
author: "roife"
date: 2022-10-16

tags: ["System Verilog@编程语言", "集成电路@Tags", "SV for Verification@读书笔记"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 循环

## `forever`

死循环，需要在另一个 `initial` 块中指定结束的时间（类似 `always` 块）。

在 `forever` 循环中必须用时延/触发条件来步进，否则整个循环会直接被挂起。

```verilog
forever // ...
```

```verilog
initial begin
    forever begin
        #5 // ...
        // 或者 @(posedge clk)
    end
end

initial begin
    #50 $finish;
end
```

## `repeat`

循环指定次数。

```verilog
repeat(5) begin
    // ...
end
```

利用 `repeat` 块可以实现等待指定的时钟周期：

```verilog
repeat(num) @(posedge clk);
```

## `for`/`while`/`do...while`

类似于 C 语言的循环。可以在循环里加入 `@(posedge clk);` 等语句表示等待某个条件。

```verilog
while (i < 10) begin
    @(posedge clk);
    // ...
end

for (int i = 0; counter < $size(a); i++) begin
    // ...
end

do begin
    // ...
end while (i < 5);
```

## `foreach`

用于遍历数组，在前面的章节提到了。

## `break`/`continue`

类似于 C 语言，用在循环中。

# 分支语句

`if-else` 语句和 `case` 语句类似于 Verilog。

## `unique-if`

使用 `unique-if` 时，如果没有一个分支匹配到，或者有多个分支匹配到时就会报错（包括 `else`）。

但是这里对条件的求值顺序是任意的（即是可并行的）。

```verilog
int x = 4;

unique if (x == 3) begin  // 报错
    // ...
end

unique if (x == 4) begin  // 报错
    // ...
end else if (x == 4) begin
    // ...
end
```

此外还有 `unique0-if`，区别在于 `unique0-if` 允许没有分支被匹配到。

## `priority-if`

**按照顺序**对条件进行求值，并且如果没有一个分支被匹配到则报错。

```verilog
priority if () begin
end
```

## `unique-case`/`unique0-case`/`priority-case`

类似于 `unique-if`/`unique0-if`/`priority-if`。

```verilog
unique case () begin
end
```

# 命名块与 `disable` 语句

可以在 `begin` 或者 `fork` 的前面或者后面加上 label，然后在 `end`/`join`/`endmodule`/`endtask`/`endfunctiond` 等语句后面（不能加在前面）加上同样的命名 label 来实现匹配。

用 `disable` 语句来退出对应的块（直接跳到对应的 `end`）。

```verilog
begin : block1
    // ...
    disable block1;
end : block1
```

# 时间刻度

SV 允许精细的时间刻度，可以用 `#1ns` 这样的语句来表示等待 1ns。

```verilog
forever #5ns clock = ~clock;
```

## `timeunit`/`timeprecision`

可以在作用域中用 `timeunit` 和 `timeprecision` 来指定时间刻度的单位。

```verilog
module top;
    timeunit 1ns;
    timeprecision 1ns;
    // ...
endmodule
```

通常时间精度只能在 `module`/`program`/`interface` 中指定，而且必须在开头指定。