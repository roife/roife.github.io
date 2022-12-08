---
layout: "post"
title: "「BUAA-CO-Lab」 Pre-01 Logisim"
subtitle: "电路仿真"
author: "roife"
date: 2020-09-26

tags: ["北航计算机组成实验@课程相关", "课程相关@Tags", "体系结构@Tags", "集成电路@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

Logisim 是课上用于模拟仿真电路的一个软件。

# 特殊部件与属性

## Splitter

- `Fan out`：表示将几路数据进行合并，或者将数据分成几路
- `Bit Width In`： 总线的数据位宽，这里不一定是输入的位宽，也有可能是合并，输出之后的位宽
- `Appearance`：器件的外观，这里选择的是左手手性还是右手
- `Bit 0-31`：用于决定总线输入中的某一位数据，将从分线管脚的哪一位输出

## Pin

- `Output？`：决定该 Pin 属于输入管脚还是输出管脚、
- `Three-state？`：表示是否支持三状态：`0`、`1`、`x`
- `Pull Behavior`：是否增加上，下拉电阻。对于输入引脚，该属性指定应如何处理来自父级电路的浮空值。该属性可以实现加法器的进位输入为 x 状态（或者不连）时，默认进位是 0（自建加法器时会用到）：
  + `unchanged`：浮空值作为浮动值发送至父级电路中
  + `pull up`：浮空值在被送入父级电路之前被转换为 1
  + `pull down`：浮空值在被送到父级电路之前被转换为 0

## Probe

- `Radix`：数据显示的进制

## Tunnel

不详述

## Clock

- `High Duration/Low Duration`：高点平与低电平的持续时间。例如，如果选择 High Duration 为 2 tick，则在一个周期内，高点平持续 2/3 周期，低电平持续 1/3 周期默认选择 1 tick 即可。

## Gates

- 数据位宽，输入数目等
- `Negate 1-5`：表示在对应的输入端口增加一个非门

## MUX

- `Disabled Output`：若选择无数据输入，则输出值的表现，可选择浮空值，或者是 0
- `Include Enable？`：是否增加使能端。如果增加使能端，在使能端有效的时候或者处于浮空状态时，均可正常工作，但若使能端处于 0 状态时，输出端口将会成为浮空状态

## Decoder

- `Three-state？`：表示是否支持三状态：`0`、`1`、`x`
- `Disabled Output`：若选择无数据输入，则输出值的表现，可选择浮空值，或者是 0
- `Include Enable？`：是否增加使能端。如果增加使能端，在使能端有效的时候或者处于浮空状态时，均可正常工作，但若使能端处于 0 状态时，输出端口将会成为浮空状态

## DMX

- `Three-state？`：表示是否支持三状态：`0`、`1`、`x`
- `Disabled Output`：若选择无数据输入，则输出值的表现，可选择浮空值，或者是 0
- `Include Enable？`：是否增加使能端。如果增加使能端，在使能端有效的时候或者处于浮空状态时，均可正常工作，但若使能端处于 0 状态时，输出端口将会成为浮空状态

## Arithmetic

包括加减乘除取负数，不详述。

## Comparator

- `Numeric Type`：表示数据的数据种类，二进制的补码形式或无符号类型

## Shifter

- `Shift Type`：移位模式
  + `Logical Left`：逻辑左移
  + `Logical Right`：逻辑右移
  + `Arithmetic Right`：算数右移
  + `Rotate Left`：循环左移
  + `Rotate Right`：循环右移

## Register

- `Trigger`：触发模式
  + `Rising Edge`：上升沿存入
  + `Falling Edge`：下降沿存入
  + `High Level`：高电平存入
  + `Low Level`：低电平存入

## Memory

编辑地址时，点击存储值显示区域以外，`Enter` 表示下一行，`Backspace` 表示上一行，`Space` 表示向下翻页，即四行。

编辑数据时 `Enter` 表示下一行，`Backspace` 表示回到上一个位置，`Space` 表示向后一个。

文件输入时，要在头部加上 `v2.0 raw`。可以用 `16*00` 表示一行出现 `16` 个 `00`。也可以用 `#` 添加注释。输入数据要和存储器的数据位宽相匹配，否则会出现数据截断。

### RAM

- `Data Interface`：控制数据传输方式
  + `One Synchronous Load/Store port`：同一个端口读写。当 `ld` 端口为 `1` 时读取，否则存储。
  + `One asynchronous Load/Store port`：同上，不用时钟。
  + `Separate load and store ports`：读写用两个端口（通常情况）

### ROM

不详述。

## Counter

- `Action On Overflow`：将要溢出时做什么
  + `Wrap Around`：变成 0（或最大值）重新开始计数
  + `Continue Counting`：继续计数
  + `Stay At Value`：保持在最大值（或最小值）（常用）
  + `Load Next Value`：从 D 端读入下一个数据

# 进阶功能

## 子电路

1. 添加子电路：`Project` → `Add Circuit`
2. 为电路添加元件和连线
3. 编辑电路外观：`Project` → `Edit Circuit Appearance`

## Wire Bundles

![导线颜色类型](/img/in-post/post-buaa-co/wire-bundles.png "wire-bundles"){:height="500px" width="500px"}

## 组合逻辑分析

Logisim 中的逻辑分析的功能可以实现组合电路，真值表，布尔表达式三者间的转换。

- 打开组合分析窗口：`Windows` → `Combinational Analysis`

生成电路时可以选择 `Use Two-Input Gates Only` 或 `Use NAND Gates Only`。

## 仿真与调试

- 打开仿真：`Simulate` → `Simulation Enabled`
- 重置仿真：`Simulate` → `Reset Simulation`
- 仿真进行一步：`Simulate` → `Step Simulation`（好用）

- 时钟前进一步：`Simulation` → `Tick Once`
- 时钟启动：`Simulation` → `Ticks Enabled`
- 改变时钟频率：`Simulation` → `Tick Frequency`

## Logging

- `Simulation` → `Logging` 可以记录每一个时刻元器件的值

# 常用电路

## 给寄存器赋初始值

注意 counter 的 `Action On Overflow` 属性要设置为 `Stay At Value`，`Maximum Value` 要设置为 `0x1`。

MUX 上部为初始值，下部为 `0`。

或门上部为之后的步骤中给寄存器赋的值。

![初始值电路](/img/in-post/post-buaa-co/logisim-register-initial-value.png "logisim-register-initial-value"){:height="200px" width="200px"}

# Logisim 自动化浅谈

Logisim 的文件实际上是一个 XML，由 3 种标签组成：
- `<circuit>` 是电路或子电路的标签，用于标记整个电路
- `<wire>` 标签用于连线，通过 `x-y` 属性定位
- `<comp>` 标签拥有 `loc` 和 `name` 属性，用于调用库元件

可以通过代码生成 XML 来实现构造重复性电路。

# 参考资料

1. [下载](http://www.cburch.com/logisim/)
2. [Beginner's tutorial](http://www.cburch.com/logisim/docs/2.7/en/html/guide/tutorial/index.html)
3. [Reference](http://www.cburch.com/logisim/docs/2.7/en/html/libs/index.html)
