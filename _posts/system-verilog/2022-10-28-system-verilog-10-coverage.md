---
layout: "post"
title: "「System Verilog」 10 覆盖率"
subtitle: "Coverage"
author: "roife"
date: 2022-10-28

tags: ["System Verilog@编程语言", "集成电路@Tags", "SV for Verification@读书笔记"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 覆盖率

SV 中可以对某个时刻的值进行采样，并且输出测试覆盖率报告。

# `covergroup`

`covergroup` 是一个用于描述覆盖采样的类型，可以被定义在 `package`/`module`/`program`/`interface`/`class` 中。其中可以包含 `coverpoint`、形式参数、触发事件、配置选项等。

一个 `covergroup` 包含的多个 `coverpoint` 会同时被采样。

```verilog
covergroup CovGrp;
    coverpoint tr.port;
endgroup
```

## 定义

通常情况下，`covergroup` 需要实例化后使用。但是当 `covergroup` 定义在类内时，可以直接使用 `covergroup` 的名字来调用，不需要实例化。

```verilog
class Transaction;
    covergroup CovPort;
        // ...
    endgroup

    initial begin
        // 类内定义的 CovPort 可以直接使用
        CovPort = new();
        CovPort.sample();
    end
endclass
```

## 触发事件

触发采样可以通过特定事件触发（例如时钟上升沿）或主动调用 `sample()` 函数触发。

```verilog
covergroup CovPort @(posedge clk);
    // ...
endgroup
```

此外，还可以通过断言来触发采样。

```verilog
cover property
    (@(posedge sb.clock) sb.write_ena==1)
        -> write_event;

covergroup @(write_event)
    // ...
endgroup
```

## 数据采样

才覆盖点上指定一个变量或者表达式时，仿真器会为可能的数值创建“桶”（bin）。例如对于 `n` 比特的变量，会创建 `2^n` 个桶。如果某个值被触发，则会在对应的桶中留下标记。

可以通过 `auto_bin_max` 来指定自动创建桶的最大值（值域会被平均分配到这些桶中），以避免创建过多的桶。

```verilog
covergroup CovPort;
    coverpoint tr.port {
        options.auto_bin_max = 10;
    }
endgroup

// 或者用作整体选项
covergroup CovPort;
    options.auto_bin_max = 10;
    coverpoint tr.port;
endgroup
```

### 条件覆盖率

用 `iff` 关键字可以指定在条件满足时采样，这样可以忽略掉部分值。

也可以使用 `start()` 和 `stop()` 方法来控制是否进行采样。

```verilog
covergroup CovPort;
    coverpoint tr.port iff (!bus_if.reset);  // 复位时停止采样
endgroup

// 或者
CoverPort.stop();
#100 bus_if.reset = 1;
CoverPort.start();
```

# 自定义仓

如果要对表达式进行采样，那么自动创建的 bin 可能会有问题（例如 3 位变量 + 4 位变量得到的最大值是 22，并不是 2 的整数幂）。此时可以自定义仓。

```verilog
covergroup CovPort;
    len: coverpoint (l1 + l2 + 5'0) { // 因为 l1 是 3 位，l2 是 4 位，结果可能为 5 位，所以这里要扩展到 5 位
        bins len[] = [0:22];          // [] 表示是独立的仓
    }
endgroup
```

对于一组 coverpoint，还可以创建不同的仓，每组仓对应不同的范围：

```verilog
covergroup CovKind;
    coverpoint tr.kind {
        bins zero = {0};        // 1 个仓代表 kind == 0
        bins lo   = {[1:3], 5}; // 1 个仓代表 1:3 和 5
        bins hi[] = [8:$];      // 8 个独立的仓 [8:15]
        bins misc = default;    // 剩下的所有值
    }
endgroup
```

用 `$` 可以表示端点，其值取决于变量的类型。例如下面的例子：

```verilog
int i;

covergroup range_cover;
    coverpoint i {
        bins neg  = {[$:-1]};
        bins zero = {0};
        bins pos  =  {[1:$]};
    }
endgroup
```

## 转移覆盖率

bin 也可以用来表示转移覆盖率，用 `(a => b)` 表示。例如下面的例子覆盖率 `0` 转移到 `1, 2, 3` 的情况：

```verilog
covergroup CovKind;
    coverpoint tr.kind {
        bins t = (0 => 1), (0 => 2), (0 => 3);
    }
endgroup
```

除此之外，还可以用下面的特殊语法：
- 组合转移 `(1, 2 => 3, 4)`：`(1 => 3), (1 => 4), (2 => 3), (2 => 4)`
- 多次转移 `(1 => 2 => 3)`
- 重复转移 `(0 => 1[*3] => 2)`：`(0 => 1 => 1 => 1 => 2)`
- 重复指定数量的转移 `(0 => 1[*3:5] => 2)`：`1` 重复 `[3:5]` 次

## 通配符 `wildcard`

在创建 bin 的时候可以用 `?` 作为通配符，以及用 `wildcard` 关键字修饰来匹配 `0`/`1`/`x`/`z`。

```verilog
covergroup CovKind;
    coverpoint tr.kind {
        wildcard bins even = {3'b??0};  // 匹配 3 位变量的偶数
    }
endgroup
```

## 忽略特定的仓

用 `ignore_bins` 关键字可以忽略特定的仓。

```verilog
covergroup CovKind;
    coverpoint tr.kind {
        ignore_bins hi = {[6, 7]}; // 忽略 6 和 7 的 bin
    }
endgroup
```

## 为不合法的仓报错

用 `illegal_bins` 关键字定义不合法的仓，一定被覆盖到了就直接报错。

```verilog
covergroup CovKind;
    coverpoint tr.kind {
        illegal_bins hi = {[6, 7]}; // 6 和 7 的 bin 不合法
    }
endgroup
```

## 交叉覆盖率

用 `cross` 可以创建交叉覆盖率。事件 `a` 和 `b` 的交叉覆盖率是指 `a` 和 `b` 同时发生的情况，对应的仓数也会相乘。

```verilog
covergroup CovKind;
    kind: coverpoint tr.kind;
    port: coverpoint tr.port;
    cross: cross kind, port;    // 交叉两种覆盖点
endgroup
```

如果在创建 `coverpoint` 为 `bins` 指定了名称，那在报告中的交叉覆盖率会直接用仓名的组合来表示交叉后的仓名。

### 计算特定情况的交叉覆盖率

用 `binsof(a)` 可以表示 bin `a` 发生的情况。

用 `&&` 可以表示这个仓同时发生的情况。

```verilog
covergroup CovKind;
    a: coverpoint tr.a {
        bins a1 = {1};
        bins a2 = {2};
    }
    b: coverpoint tr.b {
        bins b1 = {1};
        bins b2 = {2};
    }
    ab: cross a, b {
        bins a1b1 = binsof(a.a1) && binsof(b.b1);
    }
endgroup
```

### 排除部分交叉覆盖仓

用 `ignore_bins` 可以排除部分交叉覆盖仓，其中 `binsof(a) intersect {s}` 表示 bin `a` 中与 `s` 有交集的仓。

```verilog
cross kind, port {
    // 排除 kind 为 1/2/3 且 port 为 7 的交叉覆盖仓
    ignore_bins binsof(port) intersect {7}
                && binsof(kind) intersect {1, 2, 3};
}
```

# 通用 `covergroup`（参数化）

可以给 `covergroup` 加上参数，然后在实例化时传入不同的参数来创建不同的 `covergroup`。参数的方向与函数的规则相同。

```verilog
covergroup cg (int mid);
    coverpoint port {
        bins lo = {[0:mid-1]};
        bins hi = {[mid:$]};
    }
endgroup
```

还可以通过 `ref` 传入需要采样的变量。

```verilog
covergroup cg (ref bit [0:2] port, input int mid);
    coverpoint port {
        bins lo = {[0:mid-1]};
        bins hi = {[mid:$]};
    }
endgroup
```

# 覆盖选项

## 覆盖率权重

通过 `weight` 选项可以设置某组 `coverpoint` 的权重，表示占总体覆盖率的权重。

```verilog
covergroup CovKind;
    kind: coverpoint tr.kind {
        option.weight = 5;
    }
    port: coverpoint tr.port {
        option.weight = 0;  // 不占总体覆盖率的权重
    }
    cross kind, port {
        option.weight = 10;
    }
```

## 生成单独的覆盖率报告

通过 `option.per_instance` 选项可以为 `covergroup` 生成单独的覆盖率报告。

通过 `option.comment` 选项可以为 `covergroup` 添加注释。

```verilog
covergroup CovKind;
    // ...
    option.per_instance = 1;
    option.comment = $psprintf("%m");  // 在报告的注释中使用层次化路径
endgroup
```

## 覆盖次数阈值

使用 `option.at_least` 选项可以设置覆盖次数的阈值，只有当 bin 的覆盖次数达到 `at_least` 值后，才算被覆盖到了。

`at_least` 可以定义在 `coverpoint` 表示对整个组生效，也可以定义在 `cross`、`covergroup` 上表示对单个点生效。

## 打印空仓

默认情况下覆盖率报告中不会包含没有被覆盖到的仓，可以通过 `option.print_empty` 选项来打印空仓。

## 覆盖率目标

通过 `option.goal` 选项可以设置覆盖率目标，默认为 `100%`。

# 获取覆盖率

在仿真过程中，可以通过 `$get_coverage` 获取所有覆盖组的总覆盖率。

使用 `CoverGroup::get_coverage` 或 `cgInst.get_coverage` 可以获取覆盖组所有实例的覆盖率。

使用 `cgInst.get_inst_coverage` 可以获取覆盖组某个实例的覆盖率。
