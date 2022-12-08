---
layout: "post"
title: "「C++ Primer」 02 Variables and Basic Types"
subtitle: "变量和基本类型"
author: "roife"
date: 2020-01-23

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 基本类型

| type          | minimum size (bit)               |
| ------------- | ------------------------------- |
| `bool`        | `undefined`                     |
| `char`        | `8`                             |
| `wchar_t`     | `16`                            |
| `char16_t`    | `16`                            |
| `char32_t`    | `32`                            |
| `short`       | `16`                            |
| `int`         | `16`                            |
| `long`        | `32`                            |
| `long long`   | `64`                            |
| `float`       | `6` 位有效数字（`32 bits`）     |
| `double`      | `10` 位有效数字（`64 bits`）    |
| `long double` | `10` 位有效数字（`96/128 bits`）|

## 字符类型

- `char`：可放入机器基本字符集中任意字符，大小和一个机器字节一样
- `char16_t` / `char32_t`：用于存放 Unicode 字符集

字符型分为 `char`、`signed char` 和 `unsigned char`。`char` 为后二者之一，由编译器决定。

> `wchar_t` 需要 `wcout`、`wcin` 进行 IO 操作。并且需要设置 `locale`：
>
> `setlocale(LC_ALL, "zh_CN.UTF-8")`。

## `signed` 与 `unsigned`

`unsigned int` 可以缩写成 `unsigned`。

位移操作中，`unsigned` 等价于直接位移。`signed` 为带符号位移。

### 整数溢出和转换

- `unsigned` 溢出：相当于取 `%`
- `signed` 溢出：`undefined`

当 `signed` 与 `unsigned` 相加时，`signed` 会被转换成 `unsigned`。

``` cpp
unsigned u = 10;
int i = -42;
std::cout << u + i; // 4294967264

for (unsigned i=10; i>=0; --i) // 这里会死循环
```

## 类型转换

- 非布尔 → 布尔：0 变 `false`，其余变 `true`
- 布尔 → 非布尔：`false` 变 `0`，`true` 变 `1`
- 浮点 → 整数：保留整数
- 整数 → 浮点：可能有精度损失
- 有符号 → 无符号：可能会溢出

## 字面量

### 整数和浮点数

`0` 开头的是八进制，`0x` 开头的是十六进制。

整数字面量的类型：

- 十进制：带符号类型中能容纳当前字面量的最小类型
- 八进制、十六进制：带符号和无符号类型中能容纳当前字面量的最小类型

浮点数默认用 `double`，支持 `3.14`、`3.14e0`、`0.`、`0e0`、`0.001`。

### 字符和字符串

字符用 `'a'`，字符串用 `"a"`。

由于字符串末尾默认有 `'\0'`，`"a"` 的长度比 `'a'` 大 `1`。

两个相邻的字符串字面量会合并，如 `"another" "test"` 等价于 `"another test"`。

### 转义

| 转义符 | 含义       |
| ------ | ---------- |
| `\n`   | 换行       |
| `\v`   | 纵向制表符 |
| `\\`   | 反斜杠     |
| `\r`   | 回车       |
| `\t`   | 横向制表符 |
| `\b`   | 退格       |
| `\?`   | 问号       |
| `\f`   | 进纸       |
| `\a`   | 报警       |
| `\"`   | 双引号     |
| `\'`   | 单引号     |

反斜杠后跟 1\~3 个数字时表示八进制，跟 `x` 时表示十六进制，如 `\115 == \x4d == M`，但 `\1234 == \123 + 4` 两个字符，`\x1234` 表示单个字符。

### 指定字面量类型

- 字符字面量（前缀）

| 前缀 | 类型                    |
| ---- | ----------------------- |
| `u`  | `char16_t`（Unicode 16）|
| `U`  | `char32_t`（Unicode 32）|
| `L`  | `wchar_t`               |
| `u8` | `char`（UTF-8）         |

- 数字字面量（后缀）

| 后缀       | 类型                                 |
| ---------- | ------------------------------------ |
| `u / U`    | `unsigned`                           |
| `l / L`    | `long`                               |
| `ll / LL`  | `long long`                          |
| `UL / ULL` | `unsigned long / unsigned long long` |
| `f / F`    | `float`                              |
| `l / L`    | `long double`                        |

> 注意 `3.14L` 属于 `long double`。

# 变量

## 变量定义

被定义的变量可被立即使用。

``` cpp
int price = 109, discout = price * 0.5;
```

``` cpp
int i = 0; // 初始化，注意初始化 != 赋值
int i = {0};
int i{0}; // 列表初始化，不允许丢失信息，如 int i{1.2} 错误
int i(0);
```

全局内置类型的变量会被自动初始化为 `0`，局部内置类型变量为 `undefined`。类类型变量的初始值由类决定。

## `extern`

`extern` 关键字表示只声明不定义，若初始化则等价于定义，一般用于 .h 头文件中。

``` cpp
extern int i;
extern double i = 3.14; // extern 失效
```

# 指针和引用

## 引用

一般指 lvalue reference，必须要初始化。

``` cpp
int i = 1024;
int &ref = i;
ref = 1000; // ref == i == 1000
```

引用不能重复绑定。

引用的类型必须严格匹配，如 `short` 不能引用 `int`。

## 指针

``` cpp
int ival = 42;
int *p = &ival; // 定义指针
std::cout << *p + 1 << std::endl; // 解引用
```

指针可以通过 `==` 与 `!=` 进行比较。

指针的类型必须和对象的类型严格相对应。

### 空指针

空指针使用 `nullptr` 表示。

``` cpp
int *p1 = nullptr;
int *p2 = 0; // 两句话等价
int *p3 = NULL; // #include <cstdlib>
```

旧程序会用 NULL，定义在 `cstdlib` 中，值为 0。

### `void *`

`void*` 类型的指针可以存放任意类型的指针，但是需要类型转换后使用。

## 指针的引用

``` cpp
int *&p2 = p; // 对指针的引用，从右往左理解 p2 is a reference OF a pointer TO int

int &ref = *p; // 对 p 指向对象的引用
```

离变量名最近的符号决定了变量的类型。

# `const`

``` cpp
const int bufSize = 512;
```

`const` 限定的变量后续不能更改，且必须初始化。

## `extern const`

一般 `const` 对象只能用于当前文件（考虑到常量折叠和分离式编译）。

当 `const` 变量需要跨文件时（需要 `const` 的特性，但是不能常量折叠），要在头文件和代码中同时加 `extern`。

``` cpp
// 1.h
extern const ival;

// 1.cc
extern const ival = fcn();

// 2.cc
#include "1.h"

std::cout << ival << std::endl;
```

## const 引用

`const` 对象的引用必须是 **const 引用**（为了保证 `const` 的特性）。

``` cpp
const int ival = 1024;
const int &ref = ival;
```

非 `const` 对象也可以用 const 引用。

``` cpp
int ival = 1024;
const int &ref = ival;
ival = 0; // 合法，ref 也变成 0
ref = 1024; // 不合法
```

const 引用允许引用一个表达式（右值），此时编译器会暂存这个临时量（rvalue）。

``` cpp
int ival = 1;
int &ref1 = ival + 1; // 不合法
const int &ref2 = ival + 1; // 合法
const double &ref3 = ival;
```

## const 指针

指向常量的指针也可以指向非常量，但是不能通过指向常量的指针改变非常量的值。

以下几种写法需要区分：

``` cpp
int ival = 1;

int * const p1 = &ival; // p1 不可变，*p1 可变
const int * const p2 = &ival; // p2 不可变，*p2 不可变，但 ival 可变
```

采用从右往左阅读的方式，其中 `int *const p1 = &val, ival2 = 2`，`ival2` 是 `int`。

## 顶层 const 与底层 const

**顶层 const** 即指针本身是 `const` 对象，**底层 const** 即指针指向的对象是 `const` 对象。

``` cpp
const int ival = 1024; // 顶层
const int *p1 = &ival; // 底层
int *const p2 = &ival; // 顶层
const int *const p3 = &ival; // 左边底层，右边顶层
const int &ref = ival; // 包含引用的都是底层
```

含有底层 const 定义的变量只能赋值给另一个含有相同底层 const 定义的变量。也就是说，如果一个变量是 `const` 的，那么它的指针和引用都要保证它不被修改。

``` cpp
const int i = 1;
const int *const p = &i;
int *p2 = p; // 错误，p 包含了底层 const, p2 不包含
// int *const *const 的变量也不能赋值给 int *const
```

## `constexpr`

编译期能计算出值的被称为**常量表达式**，可以用 `constexpr` 声明来验证。`constexpr` 可以看做是 `const` 的加强版本，不仅保证不可变，还保证了是常量表达式。（便于编译器优化）

基本类型、引用、指针、数组等字面量类型可以用 `constexpr`，但是 `std::string` 之类的不可以。

``` cpp
constexpr int ival = 1;
constexpr int ival2 = test(); // test 必须是一个 constexpr 函数，并且会在编译期进行计算
```

### `constexpr` 与指针

`constexpr` 修饰指针时，初始值必须是编译期确定地址的变量（如全局变量、`static` 变量），或者是 `nullptr` 和 0。

`constexpr` 等价于一个顶层 const。

``` cpp
constexpr int *p = &ival; // 相当于 int *const p;
```

# 类型运算

可以用 `typedef` 或者 `using` 来定义类型的别名（alias）。

``` cpp
typedef double wages; // wages == double
typedef wages base, *p; // base == wages == double, p == *wages == *double
using Str = std::string;
```

## 指针与 `const` 与 alias

``` cpp
typedef char *pchar; // pchar == char*

const pchar pc = 0; // char * const pc;
const pchar *ppc = 0; // char * const * ppc;
```

## `auto`

`auto` 可以让编译器自行推断类型，必须赋初始值。同一句 `auto` 声明的初始值必须相同。

``` cpp
auto sz = 0, pi = 3.14; // 非法

int i = 1;
auto &n = i, *p = &i; // 非法
```

### `auto` 绑定引用变量

对于引用，`auto` 会使用原始类型。即引用属性会被忽略。

``` cpp
int i = 0, &r = i;
auto a = r; // a 为 int 而非 int&，引用被忽略
```

### `auto` 与 `const`

`auto` 会忽略顶层 const，保留指针的底层 const。（因为底层 const 是类型的一部分）如果需要顶层 const，那么要明确用 `const` 修饰。

``` cpp
const int ci = i;
auto b = ci;  // b 是 int（const 被忽略）
auto c = &i;  // d 是 int*
auto d = &ci; // e 是 const int *，底层 const 被保留
const auto e = ci; // e 是 const int
```

同样，引用绑定常量要用 `const` 修饰。

``` cpp
auto &g = 42; // 非法
const auto &h = 42; // 合法
```

### `auto` 引用

如果类型为 `auto` 引用，则是一个例外。此时顶层属性（如顶层 const）都会被保留。

``` cpp
const int i = 1;
auto &r = i; // 保留 const 属性
```

## `decltype`

`decltype` 可以声明变量的类型，但是不一定要赋相应的初始值。

`decltype` 会携带顶层 const 与引用！

``` cpp
decltype(f()) sum = x;

const int ci = 0, &cj = ci;
decltype(ci) x = 0; // const int x = 0;
decltype(cj) y = x; // const int &y = x;
```

对于解引用的变量，`decltype` 会得到引用类型。（`decltype` 区分 lvalue 和 rvalue）

``` cpp
int i = 1024, *p = &i;

decltype(*p) c = i; // int &c = i;
```

`delctype` 的结果和表达式类型密切相关。

- 当 `decltype` 内的变量作为表达式的一部分时，可以去掉引用（变成了 rvalue）
- 当 `decltype` 内的变量加上一层括号时，将会得到一个引用（因为这样成为了一个 lvalue 的表达式）

<!-- end list -->

``` cpp
int i = 1024, &r = i;
decltype(r + 0) b; // int b; 去掉了引用

decltype((i)) d = i; // int &d = i;
decltype(i) e = i; // int e = i;
decltype(a = b) d = a; // int &
```

# `struct`

``` cpp
struct SalesData {
    std::string bookNo;
    unsigned units_sold = 0;
    double revenue = 0;
}; // 注意要加分号
```

初始化可以用 `=` 或者花括号，但是不能用圆括号。（否则会被认为是定义了一个函数，需要的时候可以写成 `C v = C(args)`）

# 头文件

类的定义一般直接写在头文件中，而且类所处的头文件名应该和类名一样。

为了防止头文件被重复包含，一般使用预处理器处理重复。

``` cpp
// 在头部写上
#ifndef SALES_DATA_H
#define SALES_DATA_H // 一般还要保证头文件保护符唯一
// ...
// 在尾部写上
#endif
```
