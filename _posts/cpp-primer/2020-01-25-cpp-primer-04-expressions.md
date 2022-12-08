---
layout: "post"
title: "「C++ Primer」 04 Expressions"
subtitle: "表达式"
author: "roife"
date: 2020-01-25

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 左值与右值

简单理解：左值是对象的引用，右值是对象的值。

使用 `decltype` 时，左值的参数会返回一个引用，如 `int *p`，则 `decltype(*p) == int&`，而 `decltype(&p) == int**`。

要得到 `int`（不带引用）可以用 `decltype(*p+0)`。

# 求值顺序

对于表达式 `f1() * f2()` 或者 `std::cout << f1() << f2() << std::endl`，不能确定是哪个函数先被调用，因此运算过程不能涉及对运算对象的修改（如 `++` 操作）。

# 算术运算

| 运算符        |
| ------------- |
| 一元 `+`, `-` |
| `*`, `/`, `%` |
| 二元 `+`, `-` |

``` cpp
bool b = -true; // b == true !! 因为是 -1
```

除法运算规定符号相同为正，否则为负，商向 0 取整（切除小数），余数的符号和被除数相同。

# 逻辑和关系运算

| 运算符               |
| -------------------- |
| `!`                  |
| `<`, `<=`, `>`, `>=` |
| `==` `!=`            |
| `&&`                 |
| `||`                 |

比较运算符不能连用，如 `i < j < k`。

在指针运算中可以用 `if (p && *p)` 来保证合法。

# 赋值运算

赋值运算符满足右结合律，结果为左值。

``` cpp
int i, *p;
double d;

d = i = 3.5; // d = i = 3;
i = d = 3.5; // i = 3, d = 3.5;
d = i = p = 0; // 非法
```

# 自增和自减运算

前置返回左值，后置返回右值。

建议使用前置运算，因为后置运算需要额外保存一个为修改的值，虽然编译器会优化内置类型类型，但是对于复杂类型（如迭代器）来说，可能有性能问题。

但是在表达式中应该谨慎使用自增和自减运算，不能用 `*beg = toupper(*beg++)` 这样的表达式。

## 自增自减与解引用运算符

自增和自减运算优先级高于解引用运算，因此可以用来简化代码。

``` cpp
auto pbeg = v.begin();
// 输出第一个负数前的所有元素
while (pbeg != v.end() && *beg) {
    std::cout << *pbeg++ << std::endl; // 等价于 *(pbeg++)，解引用的是原来的 pbeg
}
```

# 成员访问运算

解引用运算符优先级高于点运算符，因此 `(*s).size()` 等价于 `*(s.size())`。

箭头运算符总是返回左值，点运算符的返回值与成员所属对象的左右值相同。

# 条件运算符

当条件运算符的两个表达式都是左值，或者都能转换成同一种左值类型时返回左值，否则返回右值。

``` cpp
int a=1, b=2;
std::string s;
double d;

a>b? a : b = 1; // 合法
a>b? 2 : a = 1; // 合法
a>b? 2 : d = 1; // 合法
a>b? 2 : s = 1; // 非法
```

条件运算符满足右结合律，可以嵌套使用。

``` cpp
finalGrade = (grade > 90) ? "high pass"
    : (grade < 60) ? "fail" : "pass";
```

条件运算符优先级低，因此使用时应该尽量加括号，如 `std::cout << ((grade < 60) ? "fail" : "pass") << std::endl`。

# 位运算符

| 运算符     |
| ---------- |
| `~`        |
| `<<`, `>>` |
| `&`        |
| `^`        |
|            |  |

位运算处理带符号类型是 UB 行为，尽量在无符号类型上使用。

在使用位运算时注意类型范围的提升，如 `unsigned char bits = 0233; bits << 8` 会被变成 `int` 类型。

右移（`>>`）时无符号类型会在左侧补 `0`，带符号类型会在左侧复制符号位或插入 `0`，视环境而定。

# `sizeof`

`sizeof` 有两种使用方式：`sizeof (type)` 或 `sizepf expr`，满足右结合律，结果是
`constexpr size_t`（编译期计算）。

- 对数组使用时会得到数组的大小，而不会转换成指针使用。若要得到数组元素的个数，可以用 `sizeof(arr) / sizeof(int)`
- 对 `std::string` 或 `std::vector` 使用只会得到固定部分的大小，不能得到元素占用空间

`sizeof` 不会计算对象具体的值，不会产生开销，也不会产生相应的错误。

注意 `sizeof` 的优先级，`sizeof a + b` 等价于 `sizeof(a) + b`。

# 逗号运算符

逗号表达式会严格从左到右求值，左右值也取决于右侧的表达式。

# 类型转换

## 算术类型转换

当既有整型又有浮点型时 → 浮点型。

### 整型提升

整数提升在大部分运算中都会发生。

- 小整型（`bool` / `char` / `signed char` / `unsigned char` / `short` / `unsigned short`） → `int` / `unsigned`
- 大整型（`wchar_t` / `char16_t` / `char32_t`）→ `int` / `unsigned` / `unsigned long` / `long long` / `unsigned long long`

规则都是提升到能容纳原值的最小类型上。

### 无符号类型

首先整型提升，然后分情况：

- 都是有符号或都是无符号：转换成较大类型
- 有符号和无符号混合：看类型大小（占用空间）
  - 当无符号 `>=` 带符号，则 → 无符号
  - 当无符号 `<` 带符号
    - 如果有符号类型的范围包含了无符号类型的范围，则 → 带符号
    - 否则全部 → 无符号

``` cpp
unsigned a = 20;
int b = -130;
if (b < a) // true，因为 b 被转换成 4294967186
```

## 数组的转换

大多数运算中，数组会被转换成指针（除了 `decltype`、`sizeof`、`typeid`、取地址符 `&`、引用）。

## 指针的转换

- `0` / `nullptr` → 任意类型
- 指向任意非常量的指针 → `void*`
- 指向任意对象的指针 → `const void*`

## `bool` 的转换

- `0` / `'\0'` / `nullptr` → `false`
- 否则 → `true`

## 常量的转换

非 `const` 的对象可以定义对应的 `const` 的指针和引用。（保证不会用指针或引用去改变对应的 `const` 变量）

``` cpp
int i = 0;

const int &j = i; // 合法
const int *p = &i; // 合法
int *pp = p, &r = j; // 非法
```

## 类类型的转换

由编译器定义，一次只能处理一个转换请求。

## 显式转换

强制类型转换的格式为 `cast-name<type>(expr)`。

- `static_cast`：任何不涉及 `const` 转换的情况都可以用，如将大范围类型转换成小范围类型，或者还原 `void*` 类型

``` cpp
double slope = static_cast<double>(j) / i;

void *p = &d;
double *dp = static_cast<double*>(p);
```

- `const_cast`：能且只能改变对象的底层 `const` 属性，常用于函数重载。去掉 `const` 属性后若修改会产生 UB

``` cpp
const char *cp;

static_cast<std::string>(cp);
const_cast<char*>(cp);
```

- `reinterpret_cast`：对底层数据重新解释（暴力修改），十分危险

``` cpp
int *ip;
char *pc = reinterpret_cast<char*>(ip); // 暴力修改类型
```

- `dynamic_cast`：运行时类型识别

- `type (expr)` 或 `(type) expr`：早期的 C++ 类型转换

# 优先级

| 运算符                         | 用法                    |
| ------------------------------ | ----------------------- |
| `::`                           | `::name`                |
| `::`                           | `class:name`            |
| `::`                           | `namespace::name`       |
| `.`                            | `object.member`         |
| `->`                           | `pointer->member`       |
| `[]`                           | `expr[expr]`            |
| `()`                           | `func(expr_list)`       |
| `()`                           | `type(expr_list)`       |
| `++`                           | `lvalue++`              |
| `--`                           | `lvalue--`              |
| `typeid`                       | `typeid(typeid)`        |
| `typeid`                       | `typeid(expr)`          |
| `explicit cast`                | `cast_name<type>(expr)` |
| `++`                           | `++lvalue`              |
| `--`                           | `--lvalue`              |
| `~`                            | `~expr`                 |
| `!`                            | `!expr`                 |
| `-`                            | `-expr`                 |
| `+`                            | `+expr`                 |
| `*`                            | `*expr`                 |
| `&`                            | `&expr`                 |
| `()`                           | `(type) expr`           |
| `sizeof`                       | `sizeof expr`           |
| `sizeof`                       | `sizeof(type)`          |
| `sizeof...`                    | `sizeof...(name)`       |
| `new`                          | `new type`              |
| `new[]`                        | `new type[size]`        |
| `delete`                       | `delete expr`           |
| `delete[]`                     | `delete[] expr`         |
| `noexcept`                     | `noexcept(expr)`        |
| `->*`                          | `ptr->*ptr_to_member`   |
| `.*`                           | `ptr.*ptr_to_member`    |
| `*`                            | `expr * expr`           |
| `\frasl`                       | `expr / expr`           |
| `%`                            | `expr % expr`           |
| `+`                            | `expr + expr`           |
| `-`                            | `expr - expr`           |
| `<<`                           | `expr << expr`          |
| `>>`                           | `expr >> expr`          |
| `<`                            | `expr < expr`           |
| `>`                            | `expr > expr`           |
| `<=`                           | `expr<=expr`            |
| `>=`                           | `expr>=expr`            |
| `==`                           | `expr==expr`            |
| `!=`                           | `expr!=expr`            |
| `&`                            | `expr & expr`           |
| `^`                            | `expr ^ expr`           |
| `|`                            | `expr | expr`           |
| `&&`                           | `expr && expr`          |
| `||`                           | `expr || expr`          |
| `? :`                          | `cond? expr : expr`     |
| `=`                            | `lvalue = expr`         |
| `*=`, `/=`, `%=`, `+=`, `-=`   | `lvalue+=expr`          |
| `<<=`, `>>=`, `&=`, `|=`, `^=` | `lvalue<<=expr`         |
| `throw`                        | `throw expr`            |
| `,`                            | `expr, expr`            |
