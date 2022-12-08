---
layout: "post"
title: "「C++ Primer」 06 Functions"
subtitle: "函数"
author: "roife"
date: 2020-01-30

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 基础

## 形参与返回值

- 形参列表为空时可以用 `void` 替代，如 `int f(void)`
- 对于用不到的形参也可以不写名字，如 `int g(int, int)`
- 函数的返回值不能是数组或函数，但是能返回它们的指针

## 局部对象与 `static` 对象

名字有作用域的概念，对象有**生命周期**的概念。

函数体内的对象在函数结束后生命周期终止，若想要局部变量生命期延长（函数调用完不被销毁），可以用 `static` 修饰。

``` cpp
size_t count_calls() {
    static size_t crt = 0; // 第一次调用时初始化，函数结束后仍然有效，不断调用会输出 1, 2, ...
    return ++crt;
}
```

静态变量如果没有初始化，会执行值初始化（内置类型初始化为 0）。

局部对象的名字可以隐藏全局对象的名字。（如外部有函数 `read()`，内部可以定义变量 `read`）

## 函数声明

函数可以多次声明而不定义，函数声明（也叫**函数原型**）无需函数体，也无需形参的名字（并且一般形参的名字会被省略）。

``` cpp
int fact(int);
int fcn(const int &);
```

函数声明一般在头文件中进行。

函数声明时形参的名字不必与定义时相同。（有点怪）

## 分离式编译

例如：在 `factMain.cc` 进行了子函数的定义，在 `main.cc` 中定义了 `main` 函数，编译指令为

``` shell
$ CC -c factMain.cc # 生成 factMain.o
$ CC -c main.cc # 生成 fact.o
$ CC factMain.o main.o -o main # 生成可执行文件 main
```

注意共享变量/函数的代码文件要用同一个头文件。

# 参数

## 引用参数

C++ 中一般用引用代替指针传参。

引用形参的用途：

- 传递形参时有些对象不支持拷贝，或者拷贝效率很低。（为了避免修改，可以再定义成 `const` 类型）
- 返回多个参数

## `const` 参数

当值形参用 `const` 修饰时，`const` 在函数的声明中会被忽略。（会影响到函数的重载）

``` cpp
void fcn(const int x);
void fcn(int x); // 算作重复定义
```

引用形参没有 `const` 修饰时，不能传入 `const` 实参与字面值。

``` cpp
void reset(int &i) { i = 0 }
int a = 1;
const int b = 1;
reset(a); // 合法
reset(b); // 非法
reset(1); // 非法

void reset(int *i) { *i = 0; }
reset(&b); // 非法
```

因此为了安全起见和兼容性，应该尽量用 `const` 修饰。

## 数组形参

数组作参数时不能拷贝，且数组会被转换成指针。

``` cpp
void print(const int*);
void print(const int []);
void print(const int [10]); // 这里的维度代表期望值，但是不一定要相符
// 三者等价

// 类型别名
typedef int ARR1[10];
using ARR2 = int [10];
void print(const ARR2);
```

因为数组会被转换成指针，因此无法知道数组的长度，此时要特殊的方法：

- 数组本身有额外标记（如字符数组以 `\0` 作为结束标记）
- 使用标准库规范（提供头指针和尾指针）
- 显式传入数组大小

``` cpp
void print(const int *beg, const int *end);

print(std::begin(arr), std::end(arr));

void print(const int arr[], size_t size);
```

注意数组作为参数时会被转化成指针，所以不能用 `range for`。

### 数组引用形参

大小固定，任意长度的数组参数要用模板。

``` cpp
void print(int (&arr)[10]); // 只能用于长度为 10 的数组
```

### 多维数组

``` cpp
void print(int (*matrix)[10], int rowSize); // 第一维随意，第二维大小固定

void print(int matrix[][10], int rowSize); // 等价定义，注意这里 matrix 还是一个指针
```

### `main` 函数参数

``` cpp
int main(int argc, char *argv[]) {}

// 运行命令 =./a.o -a 1=
// argc = 2
// argv[0] = "./a.o"
// argv[1] = "-a"
// argv[2] = "1"
```

## 可变形参的函数

如果实参类型相同，可以用 `std::initializer_list` 标准库类型，否则可以用可变参数模板。

在 C 语言中还有省略符形参，不过一般只用于 C 接口程序交互中。

### `std::initializer_list`

如果实参数量未知但是类型相同可以用 `initializer_list` 类型。

| 操作                                      | 作用                         |
| ----------------------------------------- | ---------------------------- |
| `std::initializer_list<T> lst`            | 默认初始化                   |
| `std::initializer_list<T> lst {a, b, c};` | 列表初始化，内部值为 `const` |
| `lst.size()`                              | 元素数量                     |
| `lst.begin()`, `lst.end()`                | 迭代器                       |

和 `std::vector` 的区别在于 `std::initializer_list` 中的元素为 `const` 值（即无法改变内容），且 `std::initializer_list` 元素的值不会拷贝。

> 不存在 `std::vector<const int>`

``` cpp
void error_msg(std::initializer_list<string> il) {
    for (const auto &elem: il) { // 一般使用 const auto &
        std::cout << elem << " ";
    }
}

error_msg({"functionX", "okay"});
```

### 省略符形参

``` cpp
void foo(parm_list, ...);
void foo(parm_list...);
void foo(...); // 三种形式都可以，但纯省略符的参数难以访问
```

- `void va_start(va_list ap, last)`
  : 开始读取，`last` 为第一个变量
- `type va_arg(va_list ap, type)`
  : 读取 `type` 类型的参数
- `void va_end(va_list ap)`
  : 清理
- `void va_copy(va_list dest, va_list src)`
  : 拷贝

``` cpp
#include <cstdarg>

void test(int x ...) {
    va_list ap;
    va_start(ap, x);
    std::cout << va_arg(ap, int) << " " << va_arg(ap, double), << va_arg(ap, char *) << std::endl;
    va_end(ap);
}

test(3, 1, 3.14, "hello"); // 1 3.14 hello
```

还可以用 `va_copy(va_list dest, va_list src)` 来进行拷贝。

# 返回值

## 返回引用

函数返回一个值时会将返回值拷贝（或移动）至调用点。

``` cpp
const std::string&
shorterString(const std::string &s1, const std::string &s2) {
    return s1.size() < s2.size()? s1 : s2;
}
```

返回值为引用时，不能返回局部对象（包括值形参）的引用或指针，也不能返回字面值，因为函数完成后局部对象会被释放。只能返回函数在调用之前就已经存在的对象。

返回引用时返回值是一个左值，如 `shorterString(s1, s2) = " "`。常量引用不能赋值，如 `shorterString("a", "ab")`。

## 特殊的返回值

### 列表初始化作为返回值

返回值可以是初始化列表。

``` cpp
std::vector<std::string> process() {
    // ...
    if (excepted.empty()) {
        return {"functionX", excepted};
    } else {
        return {};
    }
}
```

如果返回值是内置类型，列表中只能包含一个元素。

### `main` 函数返回值

`main` 函数可以没有返回值，默认返回 `0`。

头文件 `cstdlib` 中定义了两个常量 `EXIT_FAILURE` 和 `EXIT_SUCCESS`，分别代表失败和成功。

`main` 函数不能调用自己。

## 返回数组指针

函数不能返回数组，但是可以返回数组的指针。（所以在讨论返回数组时，永远不能忘记加 `*`。

### 类型别名定义

``` cpp
typedef int arrT[10];
using arrT = int[10];

arrT* func(int i); // 注意这里的 *
```

### 不用类型别名

格式为 `Type (*function(parameter_list)) [dimension]`。

``` cpp
int (*func(int i))[10] {} // 表示返回值为大小为 =10= 的 =int= 数组（从内向外看）
```

### 尾置返回类型

在原来放类型的地方放 `auto`，类型放在函数头尾部。

``` cpp
// 分别是返回指针和引用
auto func(int i) -> int(*)[10] {}
auto func(int i) -> int(&)[10] {}
```

### `decltype`

``` cpp
int odd[] = {1, 3, 5, 7, 9};
int even[] = {0, 2, 4, 6, 8};

decltype(odd) *funcArr(int i) { // 注意要加一个*，因为 decltype 的识别结果是数组，要转换成指针
    return (i%2)? &even : &odd;
}

std::cout << (*funcArr(i))[1] << std::endl; // 调用
```

返回引用时也可以用 `decltype((odd))` 或者 `decltype(odd) &` 将其转换为指针或引用。

# 函数重载

函数名字相同但形参不同时是重载函数。`main` 函数不能重载。

函数的形参是否存在不影响重载，顶层 `const` 也不影响重载。但是 `T` 与 `const T` 的指针和引用是有区别的。（因为顶层
`const` 调用时会自动转化，而底层 `const` 不会）

``` cpp
Record lookup(Phone phone);
Record lookup(Phone); // 重复
Record lookup(const Phone); // 重复

Record lookup(Phone *);
Record lookup(Phone *const); // 重复
Record lookup(const Phone *); // 合法

Record lookup(Phone &); // 合法
Record lookup(const Phone &); // 合法
```

## `const_cast` 与重载

`const_cast` 可以使一个 `const` 形参引用转换成非 `const` 引用（但是要先保证安全）。因此可以通过函数重载方便地定义一个非 `const` 版本。

``` cpp
std::string&
shorterString(std::string &s1, std::string &s2) {
    auto &r = shortString(const_cast<const std::string &>(s1),
                          const_cast<const std::string &>(s2));
    return const_cast<std::string&> (r);
}
```

## 重载与作用域

在当前作用域找到声明的函数时，会忽略外层作用域的函数。

``` cpp
void print(std::string);
void foo() {
    void print(int);
    print("Value"); // 非法，外层声明的 print 被内层 print 隐藏
}
```

# 特殊特性

## 默认实参

一旦一个参数被赋予了默认值，它后面的所有参数都必须有默认值。调用函数时默认值可以省略，因此要合理设计参数位置。

``` cpp
std::string screen(int ht = 24, int wid = 80, char backgrnd = ' ');

screen(66);
```

一般会将默认参数的声明放入头文件中。

### 默认实参的声明

如果在声明处定义了参数的默认值，那么在定义处就不能继续添加。（否则变成了重复声明）

``` cpp
void test(int = 1);
void test(int a = 1) {} // 重复声明
```

有默认实参的函数在声明时不能重复为同一个变量添加默认值。（此时右侧的参数必须都有默认实参）

``` cpp
std::string screen(int, int, char = ' ');
std::string screen(int, int, char = '*'); // 非法
std::string screen(int = 24, int = 80, char); // 合法
```

### 默认实参的初始值

局部变量不能作为默认参数初始值（因为默认参数初始值需要在编译期确定）。

``` cpp
void print(int x) { std::cout << x << std::endl; }
int a = 1;

int main() {
    int b = 2;
    void print(int = a); // 合法
    void print(int = b); // 非法
}
```

默认参数初始值在声明时解析，在调用时求值！

``` cpp
int a = 1, b = 2;
void print(int x = a, int y = b); // print(1, 2);

int main() {
    a = 3;
    int b = 2;
    print(); // print(3, 2); 局部变量 b 不影响函数求值，但是内层改变的全局变量会影响求值
}
```

## `inline` 和 `constexpr` 函数

`inline` 和 `constexpr` 函数的多个定义要求完全一致，因此常被放于头文件。（和 `linkage` 的过程有关）

### `inline`

`inline` 可以在调用点展开函数，减少资源占用、适合规模小、调用多、流程直接的函数。

但是编译器可以根据实际情况选择忽略 `inline`。

``` cpp
inline const std::string &
shortString(const std::string &, const std::string &);
```

### `constexpr`

`constexpr` 函数的返回值和形参都必须是字面值类型（数字，布尔，字符或字符串，`nullptr`，字面值常量类等），而且函数有且仅有一条 `return` 语句或类型别名定义语句。

``` cpp
constexpr int new_sz() { return 42; }
constexpr int foo = new_sz();
```

`constexpr` 函数被隐式地指定为 `inline` 函数。（编译器展开）

`constexpr` 函数返回值可以是常量表达式也可以不是，当参数都是常量表达式时，返回值也是常量表达式，并且此时编译期运算。（为了同一个函数不用写两遍）

``` cpp
constexpr int foo(int i) { return i + 5; }

int i;
std::cin >> i;
std::array<int, foo(5)> arr; // 合法，返回值是常量表达式，编译期得到结果
std::array<int, foo(i)> arr2; // 非法，i 不是常量表达式，运行期得到结果
```

## 预处理的调试功能

### `assert`

语法为 `assert(expr)`，如果 `expr` 为 `false` 则终止运行，否则继续运行，定义在 `cassert` 头文件中，
常用于检查 "不能发生" 的条件。

### `NDEBUG`

如果定义了预处理变量 `NDEBUG`，则 `assert` 不工作。

可以直接 `#define NDEBUG`，或者编译时 `CC -D NDEBUG main.c`。

用 `#ifndef NDEBUG...#endif` 来定义调试期运行的代码。

``` cpp
void print() {
#ifndef NDEBUG
    std::cerr << __func__ << std::endl;
#endif
}
```

C++ 中还定义了几个常用宏。

| 名称       | 作用                |
| ---------- | ------------------- |
| `__FILE__` | 文件名的字符串值    |
| `__LINE__` | 当前行的 `int` 值   |
| `__TIME__` | 编译时间的 字符串值 |
| `__DATE__` | 编译日期的字符串值  |
| `__func__` | 函数名字            |

# 函数匹配

``` cpp
void f();
void f(int);
void f(int, int);
void f(double, double = 3.14);
```

调用失败的案例如 `f(4, 256) 匹配 f(int, int) 和 f(double, double)`

- 选出候选函数
  - 与调用函数同名
  - 声明可见
- 选出可行函数
  - 形参数量相同
  - 实参对应类型相同或可转换
- 寻找最佳匹配
  - 该函数的每个参数的匹配都不劣于其他可行函数的匹配
  - 至少有一个参数的匹配优于其他函数
- 如果存在这样的函数，调用成功；否则失败，编译器报告二义性调用

## 实参类型转换（寻找最佳匹配）

匹配可以分成几个等级：

- 精确匹配：实参和形参类型相同（允许将数组和函数转换成指针，添加或删除顶层 const）
- `const` 转换（针对指针和引用）
- 类型提升（窄类型 → 宽类型）
- 算数类型转换（小整型会进行整型提升）
- 类类型转换

### 算术类型

如果没有精确匹配，进行整型提升。

``` cpp
void ff(int);
void ff(short);
ff('a'); // 调用 ff(int)
```

所有类型转换的级别都是一样的，`double → float` 与 `double → long` 没有区别。

``` cpp
void manip(long);
void manip(float);
manip(3.14);
```

### `const` 转换

编译器可以根据 `const` 来决定引用和指针的调用函数。

``` cpp
Record lookup(Account &);
Record lookup(const Account &);
const Account a;
Account b;

lookup(a); // lookup(const Account &);
lookup(b); // lookup(Account &)
```

指针还能区分顶层 const 与底层 const。

# 函数指针

函数指针的类型与其返回值和形参类型共同决定，定义方式为 `Type (*name) (parameter_list)`。

``` cpp
bool (*pf) (const std::string &, const std::string &); // 若 *pf 两侧不写括号则变为一个返回值为 bool * 的函数

pf = &lengthCompare;
pf = lengthCompare;

// 清空指针
pf = nullptr;
pf = 0;
```

可以直接用指针调用函数。

``` cpp
// 三种等价调用
bool b1 = pf("hello", "bye");
bool b2 = (*pf) ("hello", "bye");
bool b3 = lengthCompare("hello", "bye");
```

使用重载函数时，指针类型和函数类型必须**精确匹配**（包括形参列表和返回值）。

## 函数指针作形参

将函数指针作为另一个函数的形参时，可以定义为函数类型的形式，调用时会自动将函数指针转化为函数。

``` cpp
// 二者等价
void useBigger(const std::string &s1, const std::string &s2, bool pf(const string &, const string &));
void useBigger(const std::string &s1, const std::string &s2, bool (*pf)(const string &, const string &));

useBigger(s1, s2, lengthCompare)
```

## 类型别名

可以用类型别名简化定义。

``` cpp
// 二者等价，定义函数
typedef bool Func (const std::string&, const std::string&);
typedef decltype(lengthCompare) Func2;

// 三者等价，定义函数指针
typedef bool (*FuncP) (const std::string&, const std::string&);
typedef decltype(lengthCompare) *FuncP2;
using FuncP3 = bool(*)(const std::string&, const std::string&);

void useBigger(const std::string &s1, const std::string &s2, Func); // 也可以用 FuncP 调用
```

## 函数指针作返回值

但是返回一个函数指针时，类型必须要写成指针形式，编译器不会识别函数形式

``` cpp
// 可以直接用类型别名
using F = int(int *, int); // 非指针
using FP = int(*)(int *, int); // 指针

PF f1(int); // 合法
F f2(int); // 非法
F *f3(int); // 合法

int (*f4 (int)) (int *, int); // 注意返回函数的形参和函数本身形参的位置

auto f5(int) -> int(int, int);
auto fp5(int) -> int(*)(int *, int);
```

也可以用 `decltype`：`decltype(lengthCompare) *getFcn(const std::string &)`（注意不是 `(*getFcn)`）。

## 一道诡异的题

``` cpp
using A = int[10];
auto g() -> A*;
```

如何定义函数 `f` 的类型使 `f` 返回 `g` 的函数指针？

``` cpp
auto f() -> int (*(*)())[10];
```

分析：首先写出 `g` 的类型为 `g :: int(*)[10]`。

则 `&g :: int (*(*)())[10]`（分析时从内向外：指针 → 函数的指针 → 指向的函数返回指针 → 返回数组的指针）。

注意 `[]` 与 `()` 都是优先级最高，然后考虑 `*`。
