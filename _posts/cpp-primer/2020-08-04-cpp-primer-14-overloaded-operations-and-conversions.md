---
layout: "post"
title: "「C++ Primer」 14 Overloaded Operations and Conversions"
subtitle: "运算符重载和类型转换"
author: "roife"
date: 2020-08-04

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 基本概念

重载的运算符可以看做特殊的函数。

除了 `()` 运算符，其它运算符不能有默认实参。

一个重载运算符的左侧对象默认被隐式绑定在 `*this` 上，因此运算符函数的显式参数比实际数量少一个。

重载运算符必须是类的成员函数或有一个参数是类类型，因此不能定义内置类型的运算符函数，如 `int operator+(int, int)`。
只能重载已有的运算符号，不能定义新的运算符。

`+`、`-`、`*`、`&` 四个既是一元运算符又是二元运算符，根据其参数数量来判断运算符类型。

重载运算符的优先级与原操作符保持一致。

|      |       |       |         |          |            |
| ---- | ----- | ----- | ------- | -------- | ---------- |
| `+`  | `-`   | `*`   | `/`     | `%`      | `^`        |
| `&`  | `|`   | `~`   | `!`     | `,`      | `=`        |
| `<`  | `>`   | `<=`  | `>=`    | `++`     | `--`       |
| `<<` | `>>`  | `==`  | `!=`    | `&&`     | `||`       |
| `+=` | `-=`  | `/=`  | `%=`    | `^`      | `&=`       |
| `|=` | `*=`  | `<<=` | `>>=`   | `[]`     | `()`       |
| `->` | `->*` | `new` | `new[]` | `delete` | `delete[]` |
| `::` | `.*`  | `.`   | `?:`    |          |            |

调用重载函数有两种方式，直接用运算符和使用重载函数

``` cpp
data1 + data2;
operator+(data1, data2);

data1 += data2;
data1.operator+=(data2);
```

对于短路运算符逗号，`&&` 与 `||`，重载过后求值不再是短路运算；对于取地址符号一般也不重载。

对类重载运算符时，有几条一般规则：

- 如果类执行 IO 操作，操作符应该和内置 IO 类相同
- 如果定义了 `==`，那么也应该定义 `!=`
- 如果定义了 `<`，那么也应该定义剩下的操作

对于重载为成员函数还是非成员函数一般也有几条规定

- `==`、`[]`、`()`、`->` 必须为成员函数
- 复合赋值一般为成员函数，但非必须
- 递增，递减，解引用必须是成员函数（因为改变了对象本身）
- 算数，相等性，关系运算，位运算一般为非成员函数（因为要求左右可交换）

当运算符定义为成员函数时，运算符左侧必须是这个类类型

``` cpp
// + 是成员函数
std::string s = "world";
std::string t = s + "!"; // 合法
std::string u = "hello" + s; // 非法
// 当 + 为非成员函数时才可以发生隐式类型转换
```

# 运算符

## 输入输出运算符

输入输出运算符的第一个参数一般是流对象的引用（因为流无法被拷贝），第二个一般是常量引用（避免拷贝）。返回值一般为流的引用。

输入输出流必须是非成员函数，而且是 `friend`（为了访问 `private` 数据），否则输出要写作 `data << std::cout`。

``` cpp
ostream& operator<<(std::ostream &os, const Sales_data &item) {
    os << item.isbn() << " " << item.units_sold << " ";
    return os; // 返回流
}

istream& operator>>(std::istream &is, const Sales_data &item) {
    double price;
    is >> item.bookNo >> item.units_sold >> price;
    if (is) item.revenue = item.units_sold * price; // 检查输入状态
    else item = Sales_data(); // 若输入不合法则，置空
    return is;
}
```

输出时末尾一般不额外输出空格、换行等，方便用户来控制格式。

输入时要检查输入状态，若输入不合法则应该将状态置空或者其他合法状态。必要情况下要标记输入流的错误。（通常标准库能自己处理）

## 算术运算符

算术运算符一般不改变参数，所以定义为常量引用。

算术运算返回一般会借助局部变量，因此可以用复合赋值运算定义算术运算符。

``` cpp
Sales_data
operator+(const Sales_data &lhs, const Sales_data &rhs) {
    Sales_data sum = lhs;
    return sum += rhs;
}
```

## 比较运算符

定义不等运算时可以借助相等运算。

``` cpp
bool operator==(const Sales_data &lhs, const Sales_data &rhs) {
    return lhs.isbn()==rhs.isbn() &&
        lhs.unis_sold == rhs.unis_sold &&
        lhs.revenue == rhs.revenue;
}

bool operator!=(const Sales_data &lhs, const Sales_data &rhs) {
    return !(lhs == rhs);
}
```

一般定义 `<`，然后通过 `<` 来定义其它运算。

类在定义关系运算符时应该注意成员变量比较的顺序问题。

## 赋值运算符

``` cpp
StrVec& operator=(std::initializer_list<std::string>) {
    // ...
    free(); // 释放原有资源
    // ...
    return *this;
}
```

赋值操作的中要记得释放原有资源。

赋值函数一般定义为成员函数。

## 下标运算符

下标运算通常将引用作为返回值，且会定义常量与非常量两个版本

``` cpp
class StrVec {
public:
    std::string& operator[](std::size_t n) { return elements[n]; }
    const std::string& operator[](std::size_t n) { return elements[n]; } // 定义常量版本
    // ...
};
```

## 递增递减运算符

前置和后置递增递减运算符的区别在于，后置运算符会额外多出一个不使用的 `int` 参数，默认为 `0`。

``` cpp
C operator++(C &rhs) { // 前置
    // ...
    return rhs;
}

C operator--(C &rhs, int) { // 后置
    C ret = rhs;
    --rhs;
    return rhs;
}
```

显式调用时同理：`c.operator++(0)`，`c.operator++()`。

## 成员访问运算符

一般将二者定义为 `const` 成员函数。

``` cpp
std::string& operator*() const;
std::string* operator->() const {
    return &this->operator*();
}
```

对于箭头运算符，要求返回值必须是类的指针或者一个重载了 `->` 的对象。

箭头运算符实际上是一元函数，实际上 `p->mem` 等价于 `p.operator->() -> mem`，调用过程如下：

- 当 `->` 返回指针时，等价于普通的 `->`
- 当返回一个重载了 `->` 的对象时，该对象会继续调用重载的 `->` 运算符

# 函数调用运算符

类重载了函数调用运算符，那么就可以像使用函数一样使用类。（函数对象）

``` cpp
struct absInt {
    int operator()(int val) const {
        return val < 0? -val : val;
    }
};

int i = absInt(-42);
```

## 函数对象

函数对象可以利用对象保存状态。

``` cpp
class PrintString {
public:
    PrintString(std::ostream &o = std::cout, char c = ' '):
        os(o), sep(c) {}
    void operator()(const std::string &s) const { os << s << sep; }
private:
    std::ostream &os;
    char sep;
};

PrintString printer;
printer(s);
std::for_each(vs.begin(), vs.end(), PrintString(std::cout, '\n'));
```

## lambda 是函数对象

编译器会将 lambda 表达式翻译成未命名类的未命名对象，并且重载了函数调用运算符。

默认情况下 lambda 不能改变捕获的变量，因为重载的函数调用运算符是 `const` 的，必须要用 `mutable` 修饰后才能修改。

对于捕获的变量，如果是引用捕获那么会直接使用引用，如果是值引用那么会建立类成员并通过构造函数初始化。

``` cpp
auto wc = [sz](const std::string &a) { return a.size() >= sz; }

// 等价于

class SizeComp {
public:
    SizeComp(size_t n): sz(n) {}
    bool operator()(const std::string &s) const { return s.size() > sz; } // const 成员函数
private:
    size_t sz;
}
```

lambda 表达式产生的类不包含默认构造函数、赋值函数、析构函数，可能有拷贝、移动构造函数。

## 标准库函数对象

标准库定义了一组算术、关系、逻辑运算符的函数对象，定义在头文件 `functional` 中。

``` cpp
std::plus<int> intAdd;
int sum = intAdd(10, 20);
```

| 算术               | 关系                  | 逻辑                |
| ------------------ | --------------------- | ------------------- |
| `plus<Type>`       | `equal_to<Type>`      | `logical_and<Type>` |
| `minus<Type>`      | `not_equal_to<Type>`  | `logical_or<Type>`  |
| `multiplies<Type>` | `greater<Type>`       | `logical_not<Type>` |
| `divides<Type>`    | `greater_equal<Type>` |                     |
| `modulus<Type>`    | `less<Type>`          |                     |
| `negate<Type>`     | `less_equal<Type>`    |                     |

可以用函数对象结合标准库使用 `std::sort(v.begin(), v.end(), std::greater<int>())`

直接比较两个指针对象是 UB，但是可以通过标准库来比较指针对象。

``` cpp
std::vector<std::string*> nameTable;
// 错误
std::sort(nameTable.begin(), nameTable.end(),
    [](std::string *a, std::string *b){ return a < b; });

// 正确
std::sort(nameTable.begin(), nameTable.end(), std::less<std::string*>());
```

## 可调用对象

可调用对象有函数、函数指针、lambda、`std::bind`、函数对象，每个可调用对象都有自己的类型。

每个 lambda 都有自己唯一的类类型。

两个不同类型的可调用对象共享同一种调用形式（如 `int (int, int)` 可以表示所有接受两个 `int` 返回 `int` 的可调用对象），因此可以共同存储。

## 函数表

可以用 `std::map` 来实现函数表。但是要注意每个 lambda 都有单独的类型，因此要用 `std::function` 来转换。

``` cpp
std::map<std::string, int(*)(int, int)> binops;

int add(int i, int j) { return i + j; }
auto mod = [](int i, int j) { return i % j; }

binops.insert({ "+", add });
binops.insert({ "%", mod }); // 非法，lambda 表达式不能直接存储
```

## `std::function`

| 操作                                | 作用                                      |
| ----------------------------------- | ----------------------------------------- |
| `std::function<T> f;`               | 构造空的 `f`                              |
| `std::function<T> f(nullptr);`      | 显式构造空的 `f`                          |
| `std::function<T> t(obj);`          | 用可调用对象 `obj` 初始化 `f`             |
| `f`                                 | 返回 `bool`，表示 `f` 是否可以调用        |
| `f(args)`                           | 调用对象                                  |
| `std::function<T>::result_type`     | 对象的返回类型                            |
| `std::function<T>::argument_type`   | 对象的参数类型（要求只能有一个参数）      |
| `std::function<T>::first_argument`  | 对象的第一个参数类型（要求只能有两个参数）|
| `std::function<T>::second_argument` | 对象的第二个参数类型（要求只能有两个参数）|

用 `std::function` 来定义 `std::map`，就可以将 lambda 表达式存入函数表了。

``` cpp
std::function<int(int, int)> f1 = add;
std::function<int(int, int)> f2 = [](int i, int j) { return i*j; }

std::map<std::string, std::function<int(int, int)>> binops;
```

## 重载函数与 `std::function`

使用函数名字时，编译器无法识别重载函数。可以用函数指针或 lambda 表达式来消除二义性。

``` cpp
int add(int, int j);
Sales_data add(const Sales_data&, const Sales_data&);

std::map<std::string, std::function<int(int, int)>> binops;

binops.insert( {"+", add} ); // 非法，编译器无法区分
binops.insert( {"+", [](int a, int b) { return add(a, b); }} ); // 合法

int (*fp)(int, int) = add;
binops.insert( {"+", fp} ); // 合法
```

# 类型转换运算符

类型转换运算符是类的一种特殊的成员函数，负责将类类型转换为其他类型，定义格式为 `operator type() const;`。其中 `type` 可以为除 `void`、数组、函数（但是可以是数组指针或者函数指针）以外的任何类型。

类型转换运算符通常没有返回类型和形参，且被定义为 `const` 的成员函数。

尽管编译器只能执行一次用户定义的类类型转换，但是可以执行多次内置类型转换。

``` cpp
class SmallInt {
public:
    SmallInt(int i = 0): val(i) {}
    operator int() const { return val; }

private:
    std size_t val;
}

SmallInt si;

si = si + 5; // 先把 si 转换为 int，再进行加法
si = si + 3.14; // 先把 si 转换为 int，再转换为 double
```

构造函数将其它类型向类类型转换，类型转换运算符将类类型转换为其他类型。

## 显式类型转换操作符

大多数类定义了向 `bool` 转换的操作符，但是有可能会发生意想不到的错误。如为 `std::istream` 定义了向 `bool` 转换的操作符，那么 `std::cin << 42;` 中，由于 `std::cin` 未定义 `<<` 操作，所以会先转换成 `bool` 再运算，错误。

将操作符用 `explicit` 修饰能避免隐式类型转换。

``` cpp
explicit operator int() const { return val; }

return si + 3; // 非法
return static_cast<int>(si) + 3; // 合法
```

但是有例外，当表达式出现在下列位置中时，对于表达式整体可能会进行隐式类型转换。（即使类型转换是隐式的）

- `if` / `while` / `do` / `for` 的条件部分
- `!` / `&&` / `||` 的运算对象
- `?:` 的条件部分

## 类类型转换为 `bool`

一般定义类类型向 bool 转换的运算符为 `explicit operator bool`。

# 类型转换的二义性

有可能两种类型之间存在多种转换方式。

- `A` 定义了一个接受 `B` 的构造函数，同时 `B` 定义了一个 `A` 的类型转换运算符
- 定义了多个转换规则，而这些转换规则可以通过其他转换间接转换

## 构造函数与转换规则的二义性

``` cpp
struct B;

struct A {
    A() = default;
    A(const B&);
};

struct B {
    operator A() const;
};

A f(const A&);
B b;
A a = f(b); // 非法，存在二义性
```

此时需要显式指出调用的函数。

``` cpp
A a1 = f(b.operatorA());
A a2 = f(A(b));
A a3 = static_cast<A>(b); // 非法，编译器仍无法识别转换函数
```

## 与内置类型（算术类型）转换的二义性

``` cpp
struct A {
    A(int = 0);
    A(double);
    operator int() const;
    operator double() const;
};

void f2(long double);

A a;
f2(a); // 非法，二义性转换，int→long double 与 double→long double 等价

long lg;
A a2(lg); // 非法，二义性转换
```

这种情况下发生二义性转换的根本原因是内置类型转换的级别相同。

因此一般只会定义一种类类型到算术类型的转换，只定义一种算术类型为参数的构造函数。

``` cpp
short s = 42;
A a3(s); // 合法，因为 short→int 优先于 short→long double
```

## 重载函数与构造函数二义性

``` cpp
struct C {
    C(int);
};

struct D {
    D(int);
};

void manip(const C&);
void manip(const D&);

manip(10); // 非法，二义性错误
manip(C(10)); // 合法，显式转换
```

调用重载函数时，如果发生了用户定义的类类型转换，那么认为这些转换级别相同，如 `int → C` 与 `int → double → E` 级别相同。因此最好显式指出类型的转换。

## 函数匹配与重载运算符

重载的运算符也是重载的函数，与普通的函数匹配相比，重载运算符的过程还包括了成员函数与非成员函数的匹配。如 `a + b` 可能是 `a.operator+(b)` 或 `operatorA(a, b)`。
