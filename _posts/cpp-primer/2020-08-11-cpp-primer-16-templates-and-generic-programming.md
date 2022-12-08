---
layout: "post"
title: "「C++ Primer」 16 Templates and Generic Programming"
subtitle: "模板"
author: "roife"
date: 2020-08-11

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 模板定义

## 函数模板

函数模板由 `template` 和模板参数列表组成。每个类型参数前都必须加上 `typename` 或 `class`（二者含义相同）。

函数模板参数包括用到的类型或值，使用时显式或隐式指定模板实参。编译器可以利用函数实参推断模板实参，对函数进行实例化，生成的版本称为**实例**。

``` cpp
template <typename T>
int cmp(const T &v1, const T &v2) {
    if (v1 < v2) return -1;
    else if(v2 < v1) return 1;
    else return 0;
}

//  int cmp(const int&, const int &);
std::cout << cmp(0, 1) << std::endl;
```

### 非类型参数

非类型参数表示一个值而非一个类型，需要用户提供或编译期推断，因此必须是常量表达式（如果是指针或引用则必须有静态生存期，也可以是 `nullptr` 或 `0`）。

如传入数组参数时推断数组长度。

``` cpp
template <unsigned N, unsigned M>
int cmp(const char (&p1) [N], const char (&p2) [M]) {
    return strcmp(p1, p2);
}

// int cmp(const char (&p1)[3], const char (&p2)[4]);
// 注意有 '\0' 空字符
cmp("hi", "mom");
```

### `inline` 与 `constexpr` 的函数模板

`inline` 和 `constexpr` 要放在模板参数之后。

``` cpp
template <typename T> inline T min(const T&, const T&);
```

### 类型无关代码

- 函数参数必须是 `const` 引用（部分对象不允许拷贝）
- 条件判断只能用 `<`（部分对象可能不支持 `>`）

### 模板编译

模板只有实例化时才会编译。

函数模板和类模板成员函数定义都放在头文件中（为了保证模板可用）。

模板设计者要保证模板中使用的非模板参数名字都可见。

模板编译时产生的错误一般分为三个阶段。

- 编译模板：发现语法错误
- 模板使用：模板实参匹配
- 实例化：检查类型错误

## 类模板

类模板无法推断类型，因此使用者必须提供模板参数。

``` cpp
template <typename T>
class Blob {

};

Blob<std::string> names;
Blob<int> prices;
```

针对不同的模板参数会实例化出独立的类，它们之间不能互相访问。

### 类模板的成员函数

定义在类外部的成员函数也要加上 `template`。

``` cpp
template <typename T>
ret_type className<T>::member-name(parm-list);

template <typename T>
Blob<T>::Blob() : data(std::make_shared<std::vector<T>>()) {}
```

成员函数如果没有使用，则不会实例化。

### 作用域内省略模板参数

在模板类的作用域中使用类名等价于加上模板参数，即

``` cpp
template<typename T> class Blob {
    Blob xxxx; // 等价于 Blob<T> xxxx;
};
```

同样在类外定义成员函数时，也遵循“遇到类名才算进入类的原则”：

``` cpp
template<typename T>
Blob<T> // 不可以省略模板参数
Blob<T>::operator++() { // 遇到类名
    Blob ret; // 可以省略模板参数
    // ...
}
```

### 友元

1. 一对一的友元

    引用模板的一个特定实例前，必须进行模板声明。

    ``` cpp
    // 前置声明
    template <typename> class BlobPtr;
    template <typename> class Blob;

    template <typename T> class Blob {
        friend class BlobPtr<T>; // 只把相同类型的实例声明为友元

    };
    ```

    如上，`BlobPtr<char>` 只能访问 `Blob<char>`，不能访问 `Blob<int>`。

2. 一对多的友元或特定类型的友元

    ``` cpp
    template <typename T> class Pal;

    template <typename T> class C2 {
        friend class Pal<T>; // 特定类型，必须要前置类型

        friend class Pal<C>; // 特定类型，必须要前置类型

        template <typename X> friend class Pal2; // 所有类型，不需要前置类型（注意模板参数不同）

        friend class C3; // 普通友元，不需要前置声明
    };
    ```

    特定类型的友元必须要前置声明。

3. 将类型参数作为友元

    ``` cpp
    template <typename T> class Bar {
        friend T;
    };
    ```

    如 `Bar<Sales_data>` 可以把 `Sales_data` 作为友元。

### 类型别名

``` cpp
typedef Blob<std::string> StrBlob;
StrBlob blob;
```

`typedef` 必须要明确指定实例化的模板类型（因为模板并不是一个类型）。

新标准下可以用 `using` 为模板本身定义别名。

``` cpp
template<typename T> using twin = std::pair<T, T>;
twin<std::string> authors;

template<typename T> using partNo = std::pair<T, unsigned>;
```

### `static` 对象

每个实例类都有单独的 `static` 对象，因此访问时要加上类型。

``` cpp
template <typename T> class Foo {
public: static std::size_t ctr;
};

Foo<int> fi;
auto ct = Foo<int>::count(); // 正确
ct = fi.count(); // 正确
ct = Foo::count(); // 错误
```

`static` 成员函数同样只有在被使用时才实例化。

## 模板参数

### 作用域

模板参数和普通参数一样，遵循着“内层隐藏外层”，“可用范围在声明之后”等规则。但是模板内部不能用与外层模板参数相同的名字（如模板参数 `T`，然后内部还定义变量 `T`）。

``` cpp
typedef double A;
template <typename A, typename B>
void f(A a, B b) {
    A tmp a; // tmp 的类型为模板参数 A 的类型，而非 doub1e
    double B; // 与模板参数同名，非法
}
```

### 模板声明

模板声明必须包含模板参数，但是参数的名字不需要和定义中相同。（就和函数声明一样）

一般声明放在文件的最上面。

``` cpp
template <typename T> int cmp(const T&, const T&);
```

### 使用模板参数的类型成员

使用模板参数类型的类型成员（形如 `T::mem`）时，编译器不知道这是一个 `static` 成员还是一个类型成员。（因为二者都可以使用 `::` 的语法）默认会视为 `static` 成员，如果要表示类型成员，需要用 `typename` 修饰。

``` cpp
template <typename T>
typename T::value_type top(const T& c) { // 用 typename 指明类型
    if (!c.empty()) return c.back();
    else return typename T::value_type(); // 调用类型的构造函数
}
```

### 默认模板参数

类似默认函数参数。

``` cpp
template <typename T, typename F = std::less<T>> // 默认模板参数
int compare(const T &v1, const T &v2, F f = F()) { // 默认函数参数
    // ...
}

template <typename T = int>
class Number {
    // ...
};

Number <> ave; // 尖括号 <> 不能省略，要指出这是模板
```

## 成员模板

成员模板不能是虚函数。

**普通类**中的成员模板和定义在外面的模板没区别。

``` cpp
class DebugDelete {
public:
    DebugDelete(std::ostream &s = std::cerr) : os(s) {}

    template <typename T>
    void operator() (T *p) const {
        os << "deleting ptr" << std::endl;
        delete p;
    }
private:
    std::ostream &os;
};

std::unique_ptr<std::string, DebugDelete> sp(new string, DebugDelete());
```

在**模板类**中写包含另一个模板的成员函数时，若成员函数写在外部，则要跟上类本身的模板列表。实例化时，编译器会通过类和函数参数推断模板实参。

``` cpp
template <typename T> class Blob {
    template <typename It> Blob(It b, It e);
};

template <typename T>
template <typename It>
Blob<T>::Blob(It a, It b) { // 成员函数
    // ...
}

Blob<int> a2(begin(ia), end(ia)); // 实例化为 Blob<int> (int*, int*)
```

## 控制实例化

模板在使用时才实例化，因此多文件编译时每个文件都可能包含一个实例。为了减小编译的开销，可以使用**显式实例化**。

编译器遇到 `extern` 时，就不会在本文件中实例化，并且保证其它文件中有对应的实例化代码，但是在链接时进行链接。可以有多个 `extern` 声明，但是只能有一个定义。

``` cpp
extern template declaration; // 实例化声明，用来防止实例化模板
template declaration;        // 实例化定义，用来强制实例化模板
```

- 由于使用模板时就会实例化，因此要在使用前就用 `extern` 声明
- 由于模板不使用就不实例化，因此可以用实例化定义强制实例化一个版本

``` cpp
// app.cc
extern template int cmp(const int&, const int&); // extern 声明

Blob<int> a1 = {0, 1, 2, 3, 4, 5};
Blob<int> a2(a1); // 会实例化
int i = cmp(a1[0], a1[1]); // 不会实例化

// cmp.cc
// 强制实例化 int 版本的 cmp，因为它在 app.cc 中要用，而在 cmp.cc 中没用，因此不会自动实例化。
template int cmp(const int &, const int &);

// 也可以写成 template int cmp<int> (const int &, const int &);
template class Blob<int>(); // 强制实例化整个类，相反如果是自动实例化，那么只会实例化用到的函数
```

强制实例化时会实例化模板的所有成员（即使没有用到）。

# 模板实参推断

## 模板类型转换

模板参数默认可以进行两种隐式转换：

- `const` 转换：非 `const` 类型可以传递给 `const` 形参，非引用的情况下顶层 const 也会被忽略
- 数组/函数转换：如果形参不是**引用类型**，把数组和函数都看成指针
- 其它类型转换（如算术类型转换、派生类转换、用户定义的转换）都不会发生

``` cpp
template <typename T> T fobj(T, T);
template <typename T> T fref(const T&, const T&);

std::string s1("a value");
const std::string s2("another value");
fobj(s1, s2); // 合法

int a[5], b[10];
fref(a, b); // 不合法！因为参数是引用，所以二者不会被看作指针，int[5], int[10] 不匹配。
```

除了这两种类型转换，其它情况必须保证相同模板参数类型相同，如 `fobj(long, int)` 无法匹配（不允许算术类型转换）。

对于函数模板中的**非模板参数类型形参**，其它类型转换是允许发生的。（即上面的规则只对模板参数类型生效）

## 显式指定类型

显式指定类型时，会按照模板参数顺序匹配，右边的参数可忽略（因此最好将需要用户手动指定类型的参数放在模板参数的最前面，一个用途便是用于让用户指定返回类型）。

``` cpp
template <typename T1, typename T2, typename T3>
T1 sum(T2, T3);

auto c = sum<long long> (a, b); // 仅显式指定 T1
```

显示指定类型后，允许更多的类型转换。

``` cpp
long a = 1; int b = 2;
auto c1 = cmp(a, b); // 非法
auto c2 = cmp<int>(a, b); // 合法
```

## 尾置返回类型

当传入参数与模板参数不同，但是和参数相关，而且能推断出来时，可以用**尾置返回类型**（此时已经获取到参数）和 `decltype`。如传入 `int`，返回 `int&`。

``` cpp
template <typename It>
decltype(*beg) &fcn(It beg, It end) { // 错误，编译器不知道 beg 是什么
    // ...
    return *beg;
}

template <typename It>
auto fcn(It beg, It end) -> decltype(beg) { // 正确，使用尾置返回类型时可以使用参数
    // ...
    return *beg;
}
```

或者手动转换出想要的类型，即**type traits**。

| 类模板                         | 作用                               |
| ------------------------------ | ---------------------------------- |
| `std::remove_reference<T>`     | 去除所有引用                       |
| `std::add_const<T>`            | 加上 `const`（前提是非 lvalue）     |
| `std::add_lvalue_reference<T>` | 变为 lvalue                        |
| `std::add_rvalue_reference<T>` | 变为 rvalue（前提是非 lvalue）      |
| `std::remove_pointer<T>`       | 由指针取得对象类型                 |
| `std::make_signed<T>`          | 变为 `signed`                      |
| `std::make_unsigned<T>`        | 变为 `unsigned`                    |
| `std::remove_extent<T>`        | 去掉一层数组（`x[n] → x`）          |
| `std::remove_all_extents<T>`   | 去掉所有层级的数组（`x[n][n] → x`） |

``` cpp
template <typename It>
auto fcn2(It beg, It end) ->
    typename std::remove_reference<decltype(*beg)>::type { // 注意要加上 typename 指明 type 是一个类型

    // ... 上面空一行保证可读性
}
```

## 函数指针

用模板给函数指针赋值或者初始化时，编译器会根据指针类型推断模板参数类型。

``` cpp
template <typename T> int cmp(const T &, const T &);
int (*pf1)(const int &, const int &) = cmp;
```

如果未指定参数，且无法推断就会产生错误。

``` cpp
void func(int(*)(const string&, const string&));
void func(int (*)(const int&, const int&));
func(cmp)；// 非法：无法推断参数类型
func(cmp<int>); // 显式调用，合法
```

## 模板实参推断与引用

### 左右值引用

和函数参数类似，必须传递左值，但是 `const T&` 可以绑定任意类型。

``` cpp
int i = 1;
const int ci = 1;

template <typename T> void f1(T&);
f1(i); // int
f1(ci); // const int
f1(5); // 非法

template <typename T> void f2(const T&);
f2(i); // const int
f2(ci); // const int
f2(5); // const int
```

同样，右值引用只能绑定右值。

### 引用折叠

一般不允许把左值直接绑定到右值上，但是模板中是例外。（这也是 `std::move` 工作的基础）

编译器推断时有两个特殊规则

- 当左值绑定到右值引用参数时，编译器会将其推断为左值：
- 当发生引用的引用时，编译器会进行引用折叠（**有左值则左值**）
  - `X& &`, `X& &&`，`X&& &`：`X&`
  - `X&& &&`：`X&&`

``` cpp
template <typename T> void f(T &&);

int i = 1;
f(i); // T 为 int &，而不是一般认为的 int，注意此时函数参数为 int & &&，变成引用的引用，发生引用折叠
// 最后此处函数类型为 void f<int&>(int &);
```

因此既可以给右值模板参数传递右值，也可以传递左值。

编写接受右值引用的模板参数可能会造成一些意外的 bug（左值的情况），这种参数一般用于**模板转发**和**模板重载**。

## `std::move`

``` cpp
template <typename T>
typename std::remove_reference<T>::type move(T&& t) {
    return static_cast<typename remove_reference<T>::type&&>(t);
}
```

其中用 `static_cast` 可以实现左值到右值的显示转换（左值到右值不可以隐式转换）。

## 转发

有时需要将参数发送给另一个函数，但是直接调用存在类型信息缺失（已经发生了类型转换，如缺少左值性和 `const` 属性）。

此时可以将参数都定义为指向模板类型参数的右值引用：

- 首先引用可以保持 const 属性
- 其次通过引用折叠可以保持左右值属性

``` cpp
template <typename F, typename T1, typename T2>
void flip(F f, T1 &&t1, T2 &&t2) {
    f(t2, t1);
}
```

但是仍然存在一个问题，假设 `f` 的函数签名是 `void f(int &&i, int &j)`。如果使用 `flip(f, i, 42)` 就会发生错误，因为调用 `f(t2, t1)` 的 `t2` 参数是一个左值表达式，而 `i` 是右值，因此会出错。然而直接调用 `f(42, i)` 则不应该出现错误。

### `std::forward`

`std::forward` 定义在头文件 `utility` 中，可以保存原始实参的信息。调用时需要**显式**模板实参调用。

对于 `T`，`std::forward` 返回 `T&&`。利用右值模板实参中保存的类型信息，就可以还原出原始类型。

左值根据引用折叠会保持左值，否则将会变成右值。这样就保证了左值不变，而剩余情况都可以被处理为右值。

``` cpp
template <typename F, typename T1, typename T2>
void flip2(F f, T1 &&t1, T2 &&t2) {
    f(std::forward<T2>(t2), std::forward<T1>(t1));
}
```

和 `std::move` 相同，一般使用 `std::forward` 而不用 `using`。

# 重载与模板

在**函数模板**和**普通函数**重载的情况下，遵循以下匹配规则：

- 优先选择匹配度高的函数
- 如果匹配度相同，且只有一个普通函数，优先选择普通函数
- 选择模板函数时，优先选择特例化程度高的函数
- 否则调用有歧义

``` cpp
template <typename T> std::string debug_rep(const T &t);
template <typename T> std::string debug_rep(T *p);

std::string s("test");
debug_rep(&s);
// 倾向于第二个模板
// debug_rep(const std::string* &t), T1 = std::string*
// debug_rep(std::string *p), T2 = std::string
// 第一个模板进行了 const 转换（顶层 const）

const

std::string debug_rep(const std::string &s);

const std::string *sp = &s;
debug_rep(sp);
// 倾向于第二个模板
// debug_rep(const std::string *&), T1 = std::string*
// debug_rep(const std::string *), T2 = const std::string
// 两个模板都能精准匹配，第一个模板可以匹配任何类型，第二个只能匹配指针，更加特化

std::string s("hi");
debug_rep(s);
// 倾向于第三个函数
// debug_rep(const std::string* &t), T1 = std::string*
// debug_rep(const std::string *p)，非模板函数匹配
// 二者同样好，选择非模板函数

debug_rep("hi world");
// 倾向于第二个模板
// debug_rep(const char (&) [10]), T1 = char[10]
// debug_rep(const char *), T2 = const char
// debug_rep(const std::string&)
// 第三个要一次类型转换，第一个不如第二个精准
```

一般对于字符数组或字面量，不能把它们匹配到指针（因为本质是数组）。

``` cpp
std::string debug_rep(char *p) {
    return debug_rep(std::string(p));
}

std::string debug_rep(const char *p) {
    return debug_rep(std::string(p));
}
```

注意模板匹配的声明，如果模板 B 声明放在实例化之后，且 A 和 B 都能匹配，那编译器可能会直接匹配 A。所以一般会在重载处一起声明所有模板。

# 可变参数模板

可变数目的参数列表称为参数包，包含零个或多个参数，分为**模板参数包**（`class...` 或 `typename...` 开头）和**函数参数包**（一个类型后面跟省略号）函数参数包的类型为模板参数包。

编译器会为不同长度的函数调用生成不同的实例。

``` cpp
template <typename T, typename... Args>
void foo(const T &t, const Args& ... rest);

foo(1, 2); // void foo(const int&, const int &);
foo(1, 2, 3); // void foo(const int &, const int &, const int &)
```

## `sizeof...`

`sizeof...` 运算符用于获取参数包长度，返回常量表达式，不会对参数进行求值。

``` cpp
template <typename ... T>
void g(Args ... args) {
    std::cout << sizeof...(Args) << endl
              << sizeof...(args) << endl;
}
```

## 编写可变参数模板

可变参数模板通常是**递归**的，首先处理包中的第一个实参，然后处理剩下的。为了终止递归，还要定义一个**同名的非可变参数模板**。

``` cpp
template <typename T>
std::ostream &print(std::ostream &os, const T &t) {
    return os << t;
}

template <typename T, typename ... Args>
std::ostream &print(std::ostream &os, const T &t, const Args& ... rest) {
    os << t << ", ";
    return print(os, rest...);
}
```

## 包扩展

包扩展（`...`）会将指定的"模式"应用到参数包中的每一个元素，如：

``` cpp
template <typename T, typename... Args>
std::ostream& print(std::ostream &os, const T &t, const Args&... rest) { // 包扩展 1
    os << t << ' ';
    return print(os, debug_rep(rest)...); // 包扩展 2
}
// 包扩展 1 中，"const Args& rest" 是模式，应用到 rest 中的每一个元素，此处展开为 const rest1&, const rest2&, ...
// 包扩展 2 中，"debug_rep(rest)" 是模式，应用到 rest 中的每一个元素，此处展开为 debug_rep(rest1), debug_rep(rest2), ...
// 如果写成 debug_rep(rest...)，则会展开为 debug_rep(rest1, rest2, ...)
```

## 转发参数包

使用 `std::forward` 配合包扩展，如 `emplace()` 函数的实现。

``` cpp
template <typename&&... Args>
inline void
StrVec::emplace_back(Args&&... args) { // 用模板参数的右值引用保存类型信息
    std::chk_n_n_alloc();
    std::alloc.construct(first_free++, std::forward<Args>(args)...);
    // std::forward(args)... 展开为 std::forward(arg1), std::forward(arg2), ...
}
```

# 模板特例化

## 函数模板特例化

特例化模板需要给每个模板参数提供实参，并使用 `template <>` 指出。

``` cpp
template <>
int compare(const char *const &p1, const char *const &p2) {
    return strcmp(p1, p2);
}
```

函数模板的参数必须和先前声明的一个模板匹配。（如匹配 `const T&` 必须要 `const char *const &`，第一个 `const` 是 `T` 的一部分，第二个 `const` 是模板要求）

特例化的本质是实例化一个模板，而非重载它。因此，特例化不影响函数匹配。（只有选择了匹配了该函数模板后才会考虑该模板下的特化版本）

## 类模板特例化

类模板特例化和函数模板类似。

``` cpp
namespace std {
    template <>
    struct hash<Sales_data> {
        typedef size_t result_type;
        typedef Sales_data argument_type;
        size_t operator() (const Sales_data& s) const;
    };

    size_t
    hash<Sales_data>::operator() (const Sales_data& s) const {
        return hash<string>()(s.bookNo) ^ hash<unsigned>()(s.units_sold) ^ hash<double>()(s.revenue);
    }
}
```

### 类模板的偏特化

偏特化指为部分模板参数提供实参，或者为部分参数提供部分特性（如指定为指针），本质还是一个模板。

偏特化模板的名字必须与原模板相同。

``` cpp
// 提供部分参数
template <class T1, class T2>
class pair {};

template <class T1>
class pair<T1, int> {};

// 限制部分参数特性
template <class T> struct remove_reference {
    typedef T type;
};

template <class T> struct remove_reference<T&> {
    typedef T type;
};

template <class T> struct remove_reference<T&&> {
    typedef T type;
};
```

### 特例化单个成员函数

可以只特例化某个成员函数，而不特例化整个类。

当类实例化版本的参数与特例化的成员函数相同时，使用特例化的成员函数；否则使用类的成员函数。

``` cpp
template <typename T> struct Foo {
    Foo(const T &t = T()) : mem(t) { }
    void Bar() {}
    T mem;
};

template<>
void Foo<int>::Bar() {

}

Foo<std::string> fs; // 使用类的 Foo
Foo<int> fi; // 使用特例化的版本
```
