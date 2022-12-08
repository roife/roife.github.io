---
layout: "post"
title: "「System Verilog」 05 时序机制"
subtitle: "SV 中仿真的时序机制"
author: "roife"
date: 2022-10-17

tags: ["System Verilog@编程语言", "集成电路@Tags", "SV for Verification@读书笔记"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# SV 中的时序机制

![Time Step in SV](/img/in-post/post-system-verilog/time-step.png){:height="400px" width="400px"}

- Active 主要是模块的设计代码（包括 RTL，门级代码，时钟发生器等）
- Observed 是 SV 的断言
- Reactive 主要是 TB 的部分
- Postponed 对下一个时钟前的信号进行采样（只读阶段）

其中 Observed 和 Reactive 可能会进一步触发 Active，并重复这个过程。

其中 `1step` 的含义即为“下一个时钟前的第一步”，即时钟的前一个时间片的 postponed 区域。

# `@` 与 `wait`

在 SV 中可以用 `@` 和 `wait` 来实现强制同步。前者表示等待某个信号，后者表示等待某个条件成立。

```verilog
@bus.cb;                                        // 等待 bus 的 cb 信号
@(posedge bus.cb.grant or negedge bus.rst);     // 等待若干个信号
wait (bus.cb.grant);                            // 等待 bus 的 cb.grant 信号
```

# 时钟块信号的驱动

假设时钟周期为 `10ns`，在 `15ns` 和 `25ns` 的时候都有一个上升沿的信号。如果对于一个端口在 `17ns` 时驱动一个信号，在 `25ns` 时驱动一个新的信号，那么由于时钟块的特性，`17ns` 的信号会丢失。

这是因为时钟块的驱动信号在事件发生时才发出，因此 `17ns` 的信号不会立即发出，并且会被 `25ns` 的信号覆盖。

因此应该尽量**同步地**驱动信号（即只在事件发生时驱动）。可以使用下面两种语法，表示等待若干个时钟周期，并在事件发生时对信号进行驱动：

```verilog
repeat(2) @bus.cb;
bus.cb.req <= 0;

##2 bus.cb.req <= 0;
```

# 时钟发生器

一般来说应该将时钟发生器放在 `module` 中，因为 `program` 是在 reactive 区执行的，因此如果有驱动信号需要从 `program` 中开始传递，那么就会和时钟信号产生竞争。

```verilog
module clk_gen(output bit clk);
    always #5 clk = ~clk;
endmodule
```

# `#0`

如果多个块可能会发生竞争，那么使用 `#0` 可以使得其中一个块最后调度执行。

但是通常来说这是一种不好的实践，因为 `#0` 用多了可能会引发新的竞争。