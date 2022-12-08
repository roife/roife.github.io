---
layout: "post"
title: "「System Verilog」 01 数据类型"
subtitle: "SV 中的数据类型"
author: "roife"
date: 2022-10-15

tags: ["System Verilog@编程语言", "集成电路@Tags", "SV for Verification@读书笔记"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Type 与 Datatype

在 SV 中明确区分 `type` 和 `datatype`，前者指是“变量”还是“线网”，即是 `var` 还是 `wire`，后者指 2 值类型还是 4 值类型，如 `logic`、`bit`、`int` 等。

```verilog
var logic [7:0] a;

// 可以省略 var
logic [7:0] a;
```

所有的线网类型都是 4 值的。

# 基本数据类型

![basic-data-type](/img/in-post/post-system-verilog/basic-data-types.png)

- `logic` 类型
  - 可以当作 `reg` 使用（在 `always` 或者 `initial` 中驱动），也可以当作 `wire` 使用（用 `assign` 驱动）
  - 但是不能同时被多个模块驱动。被多个模块驱动的情况下只能用线网类型（比如双向传输的时候）
- 2 态信号（`bit`）只有 `0` 和 `1`，主要是可以在仿真中加快仿真速度
  - 如果一个 4 态信号被转换成 2 态信号，则高阻态 `Z` 和未知态 `X` 都会被转换成 `0`
- 类型的符号
  - 定义类似于 `int unsigned`（或者写 `reg signed`）
  - 无符号类型转换成有符号类型可以用 `si = signed' (ubyte);` 同理可以用 `unsigned' ()`
- `$bit(x)` 可以求变量 `x` 的位数


浮点数可以写成 `1.0` 或者 `1.0e0` 的形式。

# 字符串

字符串是一种特殊的数组，数组的每个元素都是一个字符。

```verilog
string <var_name> [= <string_literal>];
```

| | 操作 |
|-|-|-|
| 相等判断 | `s1 == s2`, `s1 != s2`, `s1 < s2`, ... |
| 连接 | `{s1, s2, ..., sn}` |
| 重复拷贝 | `{n {s}}` |
| 索引 | `s[i]` |
| 方法调用 | `s.method([args])` |

- 常用方法
  - `int s.len()`
  - `void s.putc(int i, char c)`：`s[i] = c`
  - `byte s.getc(int i)`：获取 `s[i]`
  - `string s.tolower()`
  - `int s.compare(s)`/`int s.icompare(s)`
  - `string s.substr (i, j)`：获取 `s[i:j+1]`

- 转换方法
  - `str.atoi()`/`str.atohex()`/`str.atooct()`/`str.atobin()`/`str.atoreal()`
  - `str.itoa(i)`/`str.hextoa(i)`/`str.octtoa(i)`/`str.bintoa(i)`/`str.realtoa(r)`

## 宏定义

### 字符串插值

SV 允许使用 `` `" `` 来进行字符串插值，比如：

```verilog
`define print(v) $display(`"variable v = %h`", v);

`print(data);  // 展开成 $display("variable data = %h", data);
```

原来需要转义，应该用 `\"`；在字符串插值中，需要用 `` `\`" ``。

```verilog
`define print(v) $display(`"variable `\`"v`\`" = %h`", v)

`print(data);   // 展开成 $display("variable \"data\" = %h", data);
```

### 标识符拼接

SV 允许使用 ` `` ` 来进行标识符拼接，类似于 C 语言的 `##`，比如：

```verilog
`define TWO_STATE_NET(name) bit name`_bit;

`TWO_STATE_NET(d00);
// 展开成 bit d00_bit;
```

# 枚举类型

## 定义

类似 C 语言

```verilog
enum          {RED=3, YELLOW, GREEN}       light_3;
// RED = 3, YELLOW = 4, GREEN = 5

enum          {RED = 4, YELLOW = 9, GREEN} light_4;
// RED = 4, YELLOW = 9, GREEN = 10 (automatically assigned)

enum          {RED = 2, YELLOW, GREEN = 3} light_5;
// Error : YELLOW and GREEN are both assigned 3

enum bit[0:0] {RED, YELLOW, GREEN} light_6;
// Error: minimum 2 bits are required
```

可以用 `typedef` 定义枚举类型。

```verilog
typedef enum {RED, YELLOW, GREEN} light_t;
```

在定义 enum 类型时，还有一种特殊的定义方法，用 `NAME[i]`表示 `NAMEi`：

```verilog
// BLACK0 = 0, BLACK1 = 1, BLACK2 = 2, BLACK3 = 3
typedef enum {BLACK[4]} color_set_3;

// RED0 = 5, RED1 = 6, RED2 = 7
typedef enum {RED[3] = 5} color_set_4;

// YELLOW3 = 0, YELLOW4 = 1, YELLOW5 = 2
typedef enum {YELLOW[3:5]} color_set_5;

// WHITE3 = 4, WHITE4 = 5, WHITE5 = 6
typedef enum {WHITE[3:5] = 4} color_set_6;
```

## 方法

Enum 提供一些特殊方法：

- `e.first()`
- `e.last()`
- `e.next()`
- `e.prev()`
- `e.num()`
- `e.name()`：显示符号名称

```verilog
enum {RED, YELLOW, GREEN} light;

light = RED;
light = light.next(); // YELLOW
```

## 枚举类型转换

Enum 是强类型的（和 C 不一样），因此不能直接用整数赋值，需要类型转换。

```verilog
typedef enum {RED, YELLOW, GREEN} light_t;

light_t light;
light = RED; // OK
light = 0; // Error
light = light_t' (0); // OK, but will not check overflow

int i = light; // Auto-cast to int

if (!$cast(light, i))         // Cast and check overflow
    $display("Cast failed.");
```

# 数组

- 数组定义
  - 可以用 `a[n]`，这等价于 `a[0:n-1]`

## 静态数组

```verilog
bit [3:0] 	data; 			// Packed array / vector
logic 		queue [9:0]; 	// Unpacked array
```

### Packed Array

Packed Array 相当于把位压缩起来，因此只能用 `bit`/`logic` 类型。

packed 的部分维度需要声明在变量之前，维度顺序是从左到右（`<s1>:<b1>` 是最高维度，`<sn>:<bn>` 是最低维度），并且维度必须用 `[msb:lsb]` 的形式声明。

```verilog
bit [<s1>:<b1>] [<s2>:<b2>][...] data;
```

```verilog
module tb;
    bit [3:0][7:0]  m_data; 	// 4 bytes, MSB is m_data[3][7]

    initial begin
        m_data = 32'hface_cafe;

        $display ("m_data = 0x%0h", m_data);
        for (int i = 0; i < $size(m_data); i++) begin
            $display ("m_data[%0d] = %b (0x%0h)", i, m_data[i], m_data[i]);
        end
    end
endmodule

// ncsim> run
// m_data = 0xfacecafe
// m_data[0] = 11111110 (0xfe)
// m_data[1] = 11001010 (0xca)
// m_data[2] = 11001110 (0xce)
// m_data[3] = 11111010 (0xfa)
```

### Unpacked Array

Unpacked Array 的维度声明在变量之后，两个相邻的元素不在同一个字中。

例如对于 `bit [7:0] a[2]`，`a[0]` 和 `a[1]` 不在同一个字中。

```
a[0]: (Empty 8 bits) | (Empty 8 bits) | (Empty 8 bits) | 7 6 5 4 3 2 1 0
a[1]: (Empty 8 bits) | (Empty 8 bits) | (Empty 8 bits) | 7 6 5 4 3 2 1 0
```

## 动态数组

动态数组是一个 unpacked array，但是维度不是在定义时确定的，而是在运行时通过 `new` 指定的。

```verilog
int [7:0] 	data[];

array = new [5];

array = '{31, 67, 10, 4, 99};

int data[] = '{31, 67, 10, 4, 99}; // 自动推断大小
```

用 `a.size()` 方法可以获取数组长度，用 `a.delete()` 可以清空数组。

动态数组和普通数组可以互相复制：
- 动态数组复制到普通数组时，要求大小相同
- 普通数组复制到动态数组时，会自动 `new`

### 动态数组扩容

只能通过重新声明。

```verilog
array = new [array.size() + 1] (array);
array[array.size() - 1] = 99;
```

## 关联数组

类似于字典。

```verilog
int array1[int];
array1 = '{1: 10, 2: 20, 3: 30};

int array2[string];
array2 = '{ "Ross" : 100,
            "Joey" : 60 };
```

常用方法：
- `int a.num()`/`int a.size()`
- `a.delete(key)`
- `int a.exists(key)`
- `int a.first(ref key)`：将第一个键存入 `key` 中，并返回是否存在第一个元素（`0` 或者 `X`）；类似有 `int last (ref index);`/`int next (ref index);`/`int prev (ref index);`

## 队列

队列类似于链表 + 数组，可以自由增删。

```verilog
bit [3:0] q1[$];
q1 = {1, 2, 3}; // 注意花括号前面没有 '

bit [3:0] q2[$] = {q1, 4}; // 相当于队列拼接
```

队列可以用 `q.insert(i, x)` 和 `q.delete(i)` 进行增删。也可以用 `push_back(x)`/`push_front(x)`/`pop_back()`/`pop_front()`。

同样，可以将静态数组和动态数组用赋值语句复制到队列中。

### Queue slice

`$` 可以用于下标索引，其中 `[$:5]` 中的 `$` 表示队列的最小值，`[5:$]` 表示队列的最大值。

```verilog
bit [3:0] q1[$];
q1 = {1, 2, 3};

bit [3:0] q2 = q1[$+1:2]; // q2 = {2, 3}
bit [3:0] q3 = q1[1:$-1]; // q3 = {1, 2}
```

## 基本操作

### 数组遍历

最普通的方法是用 `for`：

```verilog
for (int i = 0; i < $size(a); i++) begin
    // ...
end
```

但是在 sv 中常用 `foreach`：

```verilog
foreach (a[i]) begin
    // ...
end

foreach (a[i, j]) begin
    // ...
end

foreach (a[i]) begin
    foreach (a[i][j]) begin // 或者 foreach (a[,j])
        // ...
    end
end
```

注意 `foreach` 的遍历顺序和声明方式有关：
- 对于 `a[0:4]`，`foreach(a[i])` 等价于 `for (int i=0; i<5; i++)`
- 对于 `a[4:0]`，`foreach(a[i])` 等价于 `for (int i=4; i>=0; i--)`

### 复制和比较

数组可以直接进行赋值（`dst = src`）和比较（`dst == src`）。

### 赋值和初始化

字面量可以用 `'{}` 表示。

- `bit [3:0] a = '{1'b1, 1'b0, 1'b1, 1'b0};`
- `bit [3:0] a = '{4'b1010};`
- `bit [3:0] a = '{4 {1'b1}};`
- `bit [3:0] a = '{1'b1, default: 1'b0};`，即 `a = '{1'b1, 1'b0, 1'b0, 1'b0};`

数组也可以直接赋值成单个值：
- `reg [SIZE-1:0] data = '1;` 全部 bit 赋值为 `1`
- `reg [SIZE-1:0] data = 'bz;`

### 常用方法

#### `with` 语句

`with` 语句类似于 `map`，会将元素（用 `item` 指代）转换成语句后进行操作。部分方法强制使用 `with`，对于另外一些则是可选的（此时相当于 `with item`）。

下面的四种写法都是等价的。

```verilog
y = a.find_first with (item == 4);
y = a.find_first() with (item == 4);
y = a.find_first(x) with (x == 4);
```

#### 计算

- `sum()`/`product()`
- `and()`/`or()`/`xor()`

```verilog
int d[] = '{9, 1, 8, 3, 4, 4};
d.sum with (item > 7);         // 2
d.sum with ((item > 7) * sum); // 17
```

需要注意的是计算结果默认和元素的类型相同，例如单比特数组求和结果仍然是单比特，但是如果用在一个 32bit 表达式，或者结果保存在 32bit 变量里，那么计算时会自动被扩展成 32bit（类似 signness）。

或者也可以用  `with` 语句实现类型转换。

```verilog
bit a[10];

a.sum();                 // 1 bit
a.sum() + 32'd0;         // 32 bit
int total = a.sum();     // 32 bit
a.sum with (int'(item)); // 32 bit
```

#### 定位

- 可选 `with` 语句
  - `min()`/`max()`
  - `unique()`/`unique_index()`
- 必须包含 `with` 语句
  - `find()`/`find_index()`
  - `find_first()`/`find_first_index()`/`find_last()`/`find_last_index()`

#### 排序

- `reverse()`/`shuffule()` 随即重排（两个方法都不允许用 `with` 语句）
- `sort()`：升序排序
- `rsort()`：降序排序

`sort()` 可以对结构数组进行排序，比如 `c.sort(x) with({x.green, x.blue});`

# `typedef`

类似于 C 语言，定义新的数组类型（unpacked array）有点怪。

```verilog
typedef bit [31:0] uint;  // 定义 packed array: uint = bit [31:0]
typedef int fix_arr5[5];  // 定义 unpacked array: fix_arr5 = int [5]
```

# 结构体

结构体定义的语法类似于 C 语言，可以用 `'{}` 初始化，并且定义一个结构体类型需要用 `typedef`。

```verilog
typedef struct {
    int a;
    byte b;
} my_s;

my_s st = '{32'haaaa_aaaa, 8hbb};
```

类似的，对于结构体也有 packed structure，语法为 `struct packed { ... } name_s;`，可以将多个类型挤压到一起（塞到一个字里）。第一个元素作为 msb，最后一个元素作为 lsb。

# Union

同 C 语言的 union。

```verilog
typedef union { int i; read f; } num_u;

num_u u;
u.f = 0.0;
```

# 类型转换

- 静态转换（不检查值）
  - 符号性：`sign'()`/`unsigned'()`
  - 位数：`2'()`
  - 类型：`int'()`
- 动态转换：`$cast(dst_var, expr)`，如果转换失败（比如越界）会返回 `0`
  - 直接使用 `$cast(dst, src)` 即可，返回值表示转换是否成功

# 常量

一般来说有三种常量的定义方式。一种是 verilog 中的宏定义，作用域为全局；另一种是 `parameter`，其它模块使用时可以修改这个参数：

```verilog
parameter a = 0;
```

还有一种是 `const`，优点在于有作用范围。

```verilog
initial begin
    const byte colon = ":";
end
```

`parameter` 和 `localparam` 不能用在 `automatic` 中，`const` 则可以用在 `automatic` 中。

# 表达式的位宽

表达式的上下文会影响表达式计算的位宽，同时赋值语句的左侧变量也会影响表达式计算的位宽。

```verilog
bit one = 1'b1;

$displayb(one + one);        // 1'd0
bit [7:0] b8 = one + one;    // 8'd2
$displayb(one + one + 2'b0); // 2'd2
$displayb(2'(one) + one);    // 2'd2
```

# 特殊操作符

## `=?=` 与 `!?=`

`=?=` 与 `!?=` 是 Verilog-2001 中引入的新运算符，用于比较两个表达式是否相等。其中，在遇到 `X` 与 `Z` 时，二者会将其看作“通配符”，即与 `X`/`Z`/`0`/`1` 都是相等的。

```verilog
11111111 =?= 1xxxz1xz
11111111 !?= 1xxxz1x0
```

## `inside`

用 `inside` 可以判断集合关系。例如

```verilog
int array [$] = {1,2,3,4,5,6,7};

0 inside {1, 2, 3}  // false
5 inside {array}    // true
```

`inside` 运算的右侧可以包含集合。

```verilog
1 inside {[0:10]}         // true
10 inside {[0:5], [9:20]} // true
```

此外，对于集合而言，可以用 `$` 表示上界或者下界（上界还是下界取决于 `$` 的位置，表示的数值取决于类型推断）。

```verilog
bit [6:0] b;              // 0 <= b <= 127
a inside {[$:4], [20:$]}  // 0 <= b <= 4 || 20 <= b <= 127
```

## 流操作符

流操作符 `>>` 和 `<<` 用在赋值表达式右边，后面跟表达式、结构体或者数组，可以把数据打包成比特流。同时可以指定一个分段宽度（默认为比特），然后进行倒序操作。

```verilog
bit [7:0] j[4] = '{8'h0a, 8'h0b, 8'h0c, 8'h0d};

int h;
h = {>>{j}};              // 0a0b0c0d
h = {<<{j}};              // b030d050, reversed by bit
h = {<<byte {j}};         // 0d0c0b0a, reversed by byte

bit [7:0] g[4] = {<<byte {j}};  // 0d, 0c, 0b, 0a, reversed by byte
bit [7:0] b[4] = {<<4 {j}};     // reversed in 4 bit (a byte)

{>> {q, r, s, t}} = j;    // q=8'h0a, r=8'h0b, s=8'h0c, t=8'h0d
h = {>> {t, s, r, q}};    // h = 32'h0d0c0b0a
```

利用流操作符可以很方便地把字节数组打包转换成字数字，也可以反过来转换。但是使用流操作符时打包需要注意两边是否对应，例如 `bit [7:0] dst[255:0]` 应该和 `bit [255:0][7:0] dst2` 对应。

但是用流操作符把结构体转换成数组时要注意，虽然结构体本身是 unpacked 的，但是转换是“逐成员”进行的，因此不需要考虑内存对齐的问题。反过来同理。

```verilog
struct { int a; byte b; } s = '{32'haaaa_aaaa, 8'hbb};
byte b[] = {>>{st}};  // {aa aa aa aa bb}
```

# `static` 与 `automatic`

## 默认 `static`

默认情况下，Verilog 中的局部变量都是对应着电路上的一个寄存器，而不是像软件语言中的堆栈段。因此对于内部定义的一个局部变量，其对应的生命周期是 `static` 的，会在仿真的初始阶段赋初值。

```verilog
function int ret_cnt(intput a);
    int cnt = 0;      // 等价于 static int cnt = 0
    cnt += a;
    return cnt;
endfunction

ret_cnt(1);  // 1
ret_cnt(1);  // 2
```

## `automatic`

因此 SV 中引入了 `automatic` 关键字来实现自动变量创建和销毁的功能。`automatic` 关键字可以修饰 `module`/`function`/`task`/变量等。声明为 `automatic` 后，其行为就和其他语言一样，会将局部变量存储在堆栈段（因此也可以用递归了）。

```verilog
function automatic int ret_cnt(intput a);
    int cnt = 0;
    cnt += a;
    return cnt;
endfunction

ret_cnt(1);  // 1
ret_cnt(1);  // 1
```

可以用对应的 `static` 关键字强制其成为静态变量。

## `static` 初始化的一个 bug

类似的问题还出在变量初始化上：

```verilog
logic local_a = a << 2;  // BUG
```

此处 `local_a` 实际上是 `static` 的，也就是说它并不是创建的时候才分配的，而是仿真的初始阶段就计算了初值，此时 `a` 的值是错误的，因此 `local_a`  也是错误的。

正确的做法是分成两行写：

```verilog
logic local_a;
local_a = a << 2;
```