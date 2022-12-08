---
layout: "post"
title: "「System Verilog」 06 断言"
subtitle: "Assertions"
author: "roife"
date: 2022-10-17

tags: ["System Verilog@编程语言", "集成电路@Tags", "SV for Verification@读书笔记"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 断言的类型

| Type | Description |
|-|-|
| `assert` | 验证给定性质是否为真，只能用于仿真 |
| `assume` | 表示验证环境的约束条件，在形式化验证时会保证输入满足这些条件；在仿真时等价于 `assert` |
| `cover` | 用于计算功能覆盖率 |
| `restrict` | 将某个性质作为形式验证的约束；仿真时会忽略 |

# Immediate Assertions

```verilog
assert(<expression>);

assert(<expression>) [begin
	// If true
end] [else begin
	// If false
end]

// Optional assertion name
[assert_name] : assert(<expression>);
```

# Concurrent Assertions

并行断言可以在 `module`/`interface`/`program` 中使用，本质上是一个不断执行的语句。并行断言能发现在时钟沿出现的错误。

- 数据采样发生在 postponed 区域，而并行断言在**（下一个周期的）** observed 区域（因此断言检测的都是上一拍采样的值！）
- 并行断言可以同时在仿真和形式化验证中使用

```verilog
assert property (@(posedge clk) a & b);
```

# `sequence` 与 `property`

- `sequence` 描述了一组信号的时序规律，可以用于并行断言中。并且 `sequence` 可以描述多个时钟周期的信号变化。

```verilog
// Sequence syntax
sequence <name_of_sequence>
  <test expression>
endsequence

// Assert the sequence
assert property (<name_of_sequence>);
```

- `property` 可以封装很多 `sequence`，表示一组用于验证的单元

```verilog
// Property syntax
property <name_of_property>
  <test expression> or
  <sequence expressions>
endproperty

// Assert the property
assert property (<name_of_property>);
```

下面是一个例子：

```verilog
sequence s1;
    @(posedge clk) a & b;
endsequence

assert property (s1);
```

写断言时一般会先将布尔表达式按照时序组织成 `sequence`，然后将 `sequence` 封装成 `property`，最后 `assert property`。

## 断言延时 `##`

时序检查不仅需要检查信号是否正确，还要检查时序是否正确，可以用 `##` 表示时序的变换。

```verilog
sequence s1;
    @(posedge clk) a ##1 b;
    // 每个时钟上升沿会检查 a 是否为 1，如果不为 1 则断言失败
    // 如果 a 为 1，则等待一个周期再检查 b 是否为 1
endsequence
```

## `##` 的用法

`##` 有很多用法：
- `a ##n b`：`a` 为高，`n` 拍后，`b` 为高，等价于 `(a == 1) ##1 ( b == 1);`
- `a ##1 b ##0 c`：`a` 为高，下一拍，`b` 和 `c` 同时为高
- `a ##[1:5] b`：`a` 为高，在下 `1` 拍到 `5` 拍之间，至少存在一次 `b` 为高
- `a ##[1:$] b`：`a` 为高，在下 `1` 拍到仿真停止，`b` 至少存在一次为高

## 连续重复 `*`

`*` 可以表示一直持续的 `sequence`
- `a[*3]`：等价于 `a ##1 a ##1 a`
- `(a ##1 b)[*3]`：等价于 `(a ##1 b) ##1 (a ##1 b) ##1 (a ##1 b)`
- `a ##1 b[*2:3] ##1 c`：等价于 `(a ##1 (b ##1 b) ##1 c) or (a ##1 (b ##1 b ##1 b) ##1 c)`
- `a[*0]`：相当于没有

## 非连续重复 `=`

- `a[=2]` ：a恰好出现2次高，可不连续，等价于 `(!a)[*0:$] ##1 a ##1 (!a)[*0:$] ##1 a ##1 (!a)[*0:$]`
- `a ##1 b[=2] ##1 c`：`a` 为高，最后一拍 `c` 为高，二者之间 `b` 恰好出现 `2` 次高（可不连续）
- `a ##1 b[=2:5] ##1 c`：`a` 为高，最后一拍 `c` 为高，二者之间 `b` 出现 `2~5` 次高，可不连续

## 非连续跟随重复 `->`

- `a[->2]`：`a` 恰好出现 `2` 次高，且最后一拍 `a` 为高
  - 等价于 `(!a)[*0:$] ##1 a ##1 (!a)[*0:$] ##1 a`
- `a ##1 b[->2] ##1 c`：`a` 为高，最后一拍 `c` 为高，倒数第二拍 `b` 为高，且 `a` 与 `c` 之间 `b` 恰好出现可不连续的 `2` 次高
- `a ##1 b[->2:5] ##1 c`：`a` 为高，最后一拍 `c` 为高，倒数第二拍 `b` 为高，且 `a` 与 `c` 之间 `b` 出现可不连续的 `2~5` 次高

## 采样方法

- `$rose(x)`：检测 `x` 的正边沿，等价于 `(!x) ##1 x`
- `$fell(x)`：检测 `x` 的负边沿，等价于 `x ##1 (!x)`
- `$stable(x)`：检测 `x` 的稳定性
- `$changed(x)`：检测 `x` 的变化性
- `$past(x, y)`：检测 `x` 的上 `y` 拍的值

注意由于断言是在下一拍采样的值，所以在一些情况下可能与边沿变化有一个周期的差。