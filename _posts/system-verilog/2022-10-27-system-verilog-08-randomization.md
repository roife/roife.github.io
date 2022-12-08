---
layout: "post"
title: "「System Verilog」 08 随机化与约束"
subtitle: "Randomization & Constraint"
author: "roife"
date: 2022-10-27

tags: ["System Verilog@编程语言", "集成电路@Tags", "SV for Verification@读书笔记"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 随机化

可以用 `rand` 或 `randc` 来表示随机化变量。

当对象使用 `randomize()` 方法初始化时，会根据约束来初始化这些随机变量。如果随机化成功，则 `randomize` 方法返回 `1`，否则返回 `0`。

`randc` 的特殊之处在于，只有当随机范围内的所有值都被使用过后，随机值才会发生重复。

```verilog
class myPacket;
    rand   bit [1:0]    mode;
    randc  bit [2:0]    key;

    constraint c_mode1 { mode < 3; }
    constraint c_key1 { key > 2; key < 7; }
endclass

assert (pkt.randomize ());
```

随机化一般只能对整数进行，不能随机化字符串或者浮点数。范围内每个整数被随机到的概率都是相等的，并且会满足指定的**所有约束**。

## 随机化方法 `randomize`

`randomize` 的签名如下，返回值代表是否成功随机化：

```verilog
virtual function int randomize ();
```

虽然 `randomize` 方法是虚函数，但是它其实是内置的方法，因此不能被覆盖。

如果随机化失败，那么变量会保留其原始值而不会被修改。

### `pre_randomize()` 和 `post_randomize()`

`randomize` 在随机化前后会分别调用 `pre_randomize()` 和 `post_randomize()`。默认情况下这两个方法都是空的，但是可以在类中重写这两个方法。但是这两个方法都不是虚函数，只是其行为类似于虚函数（可以覆盖），因此定义时不能加上 `virtual` 修饰符。

如果 `randomize()` 失败，则不会调用 `post_randomize()`。

利用 `pre_randomize()` 可以实现手动调用概率计算函数来为非随机变量构造一些特定的分布，利用 `post_randomize()` 可以计算一些随机的误差等。

## 数组随机化

### 静态数组

静态数组随机化时会给数组中的每个元素都随机化。

```verilog
class Packet;
  rand bit [3:0]     s_array [7];
endclass

module tb;
  Packet pkt;

  initial begin
    pkt = new();
    pkt.randomize();
  end
endmodule
```

### 动态数组和队列

动态数组和队列随机化时，其长度需要进行随机化，即**长度需要进行约束**。如果不进行约束，那么默认会生成空的动态数组和队列。

```verilog
class Packet;
  rand bit [3:0]     d_array [];

  // 约束长度
  constraint c_array { d_array.size() > 5; d_array.size() < 10; }
  // 约束值
  constraint c_val   { foreach (d_array[i]) d_array[i] == i; }
endclass

module tb;
  Packet pkt;
  initial begin
    pkt = new();
    pkt.randomize();
    pkt.display();
  end
endmodule
```

## 常用随机分布函数

- `$random()`：平均分布，返回 32 位有符号随机数
- `$urandom()`：平均分布，返回 32 位无符号随机数
- `$urandom_range()`：在某个范围内的平均分布
- `$dist_exponential()`：指数分布
- `$dist_normal()`：正态分布
- `$dist_poisson()`：泊松分布
- `$dist_uniform()`：均匀分布

## 随机对象

如果需要对多个对象进行随机化，那么可以使用随机对象的句柄数组来实现。

但是注意在随机化前必须创建好所有的对象再进行随机化。对于动态数组，必须按照**最大需求量**来分配元素，然后使用约束来减小数组大小。

```verilgo
class RandStuff;
    rand int v;
endclass

class RandArray;
    rand RandStuff stuff[];

    constraint c_stuff { stuff.size() inside {[1:MAX_SIZE]}; }

    // 随机化前必须创建好所有的对象
    function new()
        stuff = new[MAX_SIZE];
        foreach (stuff[i]) stuff[i] = new();
    endfunction
endclass

RandArray rand_array;
initial begin
    rand_array = new();
    rand_array.randomize();  // 由于是动态数组，因此数组大小可能会减小
end
```

## 禁用随机化

使用 `rand_mode()` 可以禁用某个变量的随机化，返回值为随机化的开启状态。格式为：

```verilog
[class_object].[variable_name].rand_mode (0);
[class_object].[variable_name].rand_mode (1);
```

## 随机序列 `randsequence`

`randsequence` 可以按照 BNF 文法生成随机序列。这样可以得到一个上下文无关文法构成的随机事件序列：

```verilog
initial begin
    for (int i=0; i<15; ++i) begin
        randsequence (stream)
            stream : cfg_read := 1 |
                     io_read  := 2 |
                     mem_read := 5 ;
            cfg_read: { cfg_read_task; } |
                      { cfg_read_task; } cfg_read;
            mem_read: { mem_read_task; } |
                      { mem_read_task; } mem read;
            io_read:  { io_read_task; } |
                      { io_read_task; } io_read;
        endsequence
    end // for
end
```

## `randcase`

`randcase` 可以用来随机选择一个分支，其中的标签标识了分支的权重。

```verilog
randcase
    1: // ... 10%
    8: // ... 80%
    1: // ... 10%
endcase
```

# 约束

约束的语法为

```verilog
constraint  [constraint_name] {  [expression 1];
                                 [expression N]; }
```

空的约束块没有影响。

多个约束块之间不允许存在冲突（否则必须在使用时禁用掉一些约束块）。

## 外部约束

约束也可以定义在类的外部，分为隐式外部约束和显式外部约束（需要加上 `extern`）。

隐式约束如果没有定义，那么可能会触发警告。显式约束如果没有被定义，则会触发错误。

```verilog
class myPacket;
    rand   bit [1:0]    mode;
    constraint c_implicit;
    extern constraint c_explicit;
endclass

constraint c_implicit { mode < 3; }
constraint myPacket::c_explicit { mode < 3; }
```

## 约束表达式

### 关系运算符

- `fixed == 5`
- `min > 3`

注意约束内部仍然是普通的表达式，因此不能写 `1 < a < 10`。

### `inside` 运算符

- `inside` 运算符：`t inside {32, 64, 128}`/`t inside {[32:256]}`（`t >= 32; t <= 256`）
- `! inside` 即不属于某个范围：`! (t inside {32, 64, 128})`

具体见 `inside` 运算符。

### 加权概率分布

利用加权分布可以改变随机的概率

有两种运算符 `:=` 和 `:/`，其区别体现在区间的权重上：
- `a := p` 与 `a :/ p` 都表示 `a` 的权重为 `p`
- `[a:b] := p` 表示 `[a:b]` 中**每个数字的权重都为 `p`**
  - 例如 `[0:3] := 20` 表示 `[0:3]` 总权重为 `20`，每个值权重为 `5`
- `[a:b] :/ p` 表示 `[a:b]` 总权重为 `p`，即其中每个数字的权重为 `p / (b - a + 1)`
  - 例如 `[0:3] :/ 20` 表示 `[0:3]` 总权重为 `20`，每个值权重为 `5`

### 条件蕴含 `->`

有两种方法可以表示出蕴含关系：`->` 与 `if`。`a -> b` 等价于 `!a || b`。

```verilog
constraint c_mode { mode == 2 -> len > 10; }
constraint c_mode_2 {
    if (mode == 2) {
        len > 10;
    }
}
```

对于 `if` 而言，还可以使用 `if...else` 表示条件不成立时的约束。

```verilog
constraint c_mode_3 { if (mode == 2) len > 10; else len < 10; }
```

### 循环约束 `foreach`

利用 `foreach` 可以对数组和队列进行约束

```verilog
rand bit[3:0] array [5];

constraint c_array { foreach (array[i]) { array[i] == i; } }
```

对于多维动态数组，部分仿真器也支持对内部维度进行单独约束：

```verilog
rand bit[3:0] md_array [][];

constraint c_md_array {
   md_array.size() == 2;

   foreach (md_array[i]) {
        md_array[i].size() inside {[1:5]};  // 对内部动态数组长度进行约束

        foreach (md_array[i][j]) {
             md_array[i][j] inside {[1:10]};
        }
    }
}
```

此外，SV 还支持对于数组的**规约运算**创建约束：

```verilog
// 约束数组元素总和为 20
constraint c_sum { array.sum() with (int'(item)) == 20; }
```

### 引导概率分布 `solve...before`

默认情况下，所有随机变量都是同时进行随机的。利用 `solve...before...` 可以改变随机的顺序，从而改变随机变量的分布。

`solve a before b` 表示先对 `a` 进行随机，然后按照约束对 `b` 进行随机。

```verilog
rand  bit           a;
rand  bit [1:0]     b;

constraint c_1 { a -> b == 3'h3; }

// 使用 solve...before
constraint c_2 { a -> b == 3'h3; solve a before b; }
```

对于 `c_1` 而言，随机变量的分布如下：

| a | b | P(c_1) |
|-|-|-|
| 0 | 0 | 1/(1 + 2^2) |
| 0 | 1 | 1/(1 + 2^2) |
| 0 | 2 | 1/(1 + 2^2) |
| 0 | 3 | 1/(1 + 2^2) |
| 1 | 3 | 1/(1 + 2^2) |

对于 `c_2` 而言，随机变量的分布如下：

| a | b | P(c_1) |
|-|-|-|
| 0 | 0 | 1/2^2 |
| 0 | 1 | 1/2^2 |
| 0 | 2 | 1/2^2 |
| 0 | 3 | 1/2^2 |
| 1 | 3 | 1/2 |

## 静态约束

静态约束类似于静态变量，可以在类的不同实例间共享。

```verilog
static constraint [constraint_name] [definition]
```

静态约束的作用主要体现在**启用或禁用约束**时，即使用 `constraint_mode()` 时。

当普通约束被打开时，只会影响到当前实例。而静态约束则会影响到所有实例的约束开启状态。

## 内嵌约束 `with`

将 `randomize()` 和 `with` 结合可以对随机变量进行额外约束（注意，不是覆盖原有约束）。

由于这里是指定约束，所以应该用 `with {}` 而非 `with()`。

```verilog
itm.randomize() with { id < 10; }
```

需要注意的是，添加的额外约束可能会和原有约束冲突而导致随机失败。

## 软约束

普通的约束被称为硬约束（hard constraints），因为随机化时必须满足所有约束。而软约束（soft constraints）则是一种**尽量满足**的约束。即如果约束之间有冲突，那么软约束允许不被满足。

```verilog
class ABC;
  rand bit [3:0] data;

  constraint c_data { soft data >= 4; // 软约束
                      data <= 12; }
endclass

module tb;
  ABC abc;

  initial begin
    abc = new;
    abc.randomize() with { data == 2 };
  end
endmodule
```

## 禁用约束

使用 `constraint_mode(0 / 1)` 可以对约束进行开关，返回约束的当前状态。格式为：

```verilog
class_obj.const_name.constraint_mode(0); // 关闭约束
class_obj.const_name.constraint_mode(1); // 开启约束

status = class_obj.const_name.constraint_mode(); // 返回状态
```