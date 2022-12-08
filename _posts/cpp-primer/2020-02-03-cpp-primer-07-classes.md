---
layout: "post"
title: "「C++ Primer」 07 Classes"
subtitle: "类"
author: "roife"
date: 2020-02-03

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 抽象数据类型

## 定义成员函数

成员函数的声明必须在类的内部，定义可以在类的外部；非成员函数的定义和声明都在类的外部。

定义在类内部的函数都是隐式的 `inline` 函数。

### `this` 指针

成员函数可以通过隐式参数 `this` 来访问所在的对象地址。

直接使用所在对象的成员，等价于对 `this` 的隐式引用。

``` cpp
// 二者等价
std::string isbn() const { return this->bookNo; }
std::string isbn() const { return bookNo; }
```

`this` 是隐式定义的常量指针，类型为 `ClassName *const`。不允许自定义名为 `this` 的参数或变量，也不允许修改 `this`。

### `const` 成员函数

当 `const` 写在函数后面时，意味着不能在函数里面修改对象的成员值。此时 `this` 指针被定义为 `const ClassName *const`，即 `*this` 为底层 const。

`const` 对象只能用 `const` 成员函数，`const` 成员函数调用其它成员函数时也要求是 `const` 的。

``` cpp
std::string isbn() const { return this->bookNo; }
```

### 类的作用域

类本身就是一个作用域。

类中的成员函数使用其他成员时可以不用在意成员定义的次序。（编译器先处理所有的声明再处理函数体）

### 外部成员函数

类外部定义成员函数时，定义（返回值，参数列表，函数名）必须和类内匹配。而且要表明所属的类，`const` 成员函数也要注明`const` 属性。

在类名之后的部分都在类的作用域中，不需要用 `this` 显式指出。

``` cpp
double Sales_data::avg_price() const { return units_sold? revenue/units_sold : 0; }
```

### 返回 `this` 对象（返回左值）

返回 `*this` 时，返回类型为一个引用，即一个左值。

``` cpp
Sales_data& Sales_data::combine(const Sales_data &rhs) {
    units_sold += rhs.units_sold;
    revenue += rhs.revenue;
    return *this;
}
```

## 类的非成员函数

类的非成员函数通常和类声明在同一个头文件中，方便调用。

特别地，定义输入输出流的函数时，应该在参数和返回值中定义成普通引用（因为会改变流的内容）。

``` cpp
std::istream &read(std::istream &is) {
    // ...
    return is;
}

std::ostream &print(std::ostream &os) {
    // ...
    return os;
} // 输出函数最好不包括换行，格式由用户控制
```

## 构造函数

构造函数用于初始化对象。

构造函数的名字和类名相同，但是没有返回类型，可以被重载，且不能被声明成 `const`（否则无法修改对象）。

`const` 对象直到构造函数完成才会获得 `const` 属性，因此构造函数可以向成员写值。

``` cpp
class Screen {
    Screen(): i(1) {}
    int i;
}

const Screen scr; // scr
```

### 合成默认构造函数

默认构造函数（即不提供参数的构造函数）会将对象默认初始化。

合成默认构造函数不需要任何实参，由编译器合成。如果有对象有初始值，合成默认构造函数会用初始值初始化；否则会默认初始化。

合成默认构造函数有几个缺点：

- 只有一个构造函数也没定义的情况下，编译器才会合成默认构造函数。一旦定义了一个构造函数（不一定是默认构造函数），就无法使用合成默认构造函数。
- 合成默认构造函数初始化对象时，一些对象（比如内置基础类型在局部中被默认初始化）的值可能是未定义的
- 类成员没有或不可访问**默认构造函数**、**析构函数**或有有未初始化的引用对象或 `const` 对象，则无法合成默认构造函数

### 初始值列表

用于初始化变量，未被初始化的变量会通过合成默认构造函数初始化。

``` cpp
Sales_data(const std::string &s, unsigned n, double p): bookNo(s), units_sold(n), revenue(p*n) {}
```

构造函数最好不重新初始化已有的初始值，但是任何一个构造函数最好都应该初始化所有没有初始值的变量。

# 访问控制和封装

可以用访问说明符 **public** 和 **private** 进行封装。访问说明符可以出现一次或多次，作用范围到下一个说明符或结尾位置。

`struct` 和 `class` 的区：

- `struct` 默认为 `public`
- `class` 默认为 `private`

## 友元 `friend`

外部无法访问 `private` 的对象，但是可以声明为友元来允许外部的类或者函数访问 `private` 成员。

友元可以声明在类内部的任意位置，不受访问控制的约束（一般在类的头部或者尾部集中声明 `friend`）。

``` cpp
class Sales_data {
    friend std::istream &read(std::istream&, Sales_data&); // 定义 friend
public:
    // ...
private:
    // ...
};

std::istream &read(std::istream&, Sales_data &) { /*...*/ } // 可以访问 private 对象
```

友元声明只是声明了访问权限，因此友元函数通常会在类的外部再进行一次函数声明。

友元函数和类的声明放在同一个头文件中，并且可以在类的声明之后。

# 类的更多特性

## 类成员

### 类型成员

类型定义也受访问权限的控制。

在类内定义类型时必须先定义再使用，因此通常将类型定义在类的开头。

### `inline`

类内定义的函数自动 `inline`，其他函数需要显式声明。

在声明和定义中只要一个加 `inline` 即可，不过最好只在类外部（定义）的地方添加（方便理解）。

通常 `inline` 函数和类也放在同一个头文件中。

### `mutable`

用 `mutable` 修饰的变量永远可以被修改（即使是 `const` 对象或函数是 `const` 成员函数）。

``` cpp
class Screen {
public:
    void func() const;

private:
    mutable size_t access_ctr;
};

void Screen::func() const { ++access_ctr; } // 合法
```

### 类内对象初始化

初始化可以用 `=` 与 `{}`，但是不能用 `()` 初始化。（会被当作一个函数）

``` cpp
class A {
    std::vector<int> v = std::vector<int> (10);
};
```

## `*this` 作返回值

成员函数返回引用可以实现链式的调用，如 `screen.move(4, 0).set('#')`，注意函数定义要用 `Screen &`。

### `const` 成员函数返回 `*this`

`const` 成员函数返回的 `*this` 指向 `const` 对象，无法进行修改（实现链式调用），此时可以进行重载 `const` 成员函数。

``` cpp
class Screen {
public:
    Screen &display(std::ostream &os) { do_display(os); return *this; }
    const Screen &display(std::ostream &os) const { do_display(os); return *this; }

private:
    void do_display(std::ostream &os) const { os << contents; }
};
```

在某个对象上调用 `display` 时，会根据它是否是 `const` 对象而调用对应的函数。（非 `const` 对象对非 `const` 成员函数的匹配度更高）

> 此处应用一个额外的 `private` 函数 `do_display() const` 实现 `public` 函数的操作。一方面辅助函数会被 `inline`，没有额外开销；另一方面有利于代码复用。但是注意为了 `const` 成员函数和非 `const` 成员函数都能调用它，因此需要定义其为 `const` 成员函数。

## 类类型

可以把 `class` 或者 `struct` 跟在类名前面进行对象的声明。

``` cpp
// 二者等价
Sales_data item1;
class Sales_data item2; // C 语言常用
```

### 类类型的声明

一个类类型如果只有声明没有定义则被称为不完全类型，声明被称为前向声明。

``` cpp
class Screen;
```

可以定义指向它的**指针**或**引用**，也可以声明（不能定义）以它为参数或返回值的**函数**。但是不能创建它的对象，或者用指针或引用去访问它（因为编译器不知道它占用的空间）。

一个类的成员类型不能是这个类，但是可以是这个类类型的指针或引用。

``` cpp
class Link_screen {
    Screen window;
    Link_screen *next, *prev;
};
```

## 友元

### 类之间的友元

``` cpp
class Screen {
    friend class Window_msg; // Window_msg 可以访问 Screen 的 private 成员，但反过来不可以
}
```

友元是单向的，而且不具有传递性（如 `A` 是 `B` 的友元，`B` 是 `C` 的友元，但是 `A` 不能访问 `C`）。

### 其它类的成员函数作为友元

``` cpp
class Screen {
    friend void Window_msg::clear(ScreenIndex);
    // ...
}
```

这样做时程序的结构必须被严格组织：

- 首先声明 `Window_msg` 类，并且不定义 `clear()`（因为要友元声明，但是还没定义过 `Screen` 类）
- 然后定义 `Screen` 类
- 最后定义 `Window_msg::clear()` 函数

### 函数重载与友元

两个重载的函数要分别定义友元。

### 友元声明与作用域

类和非成员函数的声明可以不在友元声明之前（类的成员函数友元的声明则必须在前面，不完全类型不可用做友元的声明），但是调用之前必须声明。即使友元函数定义在类的内部，也必须在外部声明后才能使用。

``` cpp
struct X {
    friend void f() {} // 友元函数的定义在类的内部
    X() { f(); } // 非法
    void g();
};

X::g() { f(); } // 非法
void f() {}
X::h() { f(); } // 合法
```

友元声明只声明了一种控制权关系，不等同于函数声明。

# 类的作用域

在类外部使用类成员时必须注明对象或作用域。

``` cpp
// pos 是 class Screen 中定义的类型
Screen::pos ht = 24;
Screen scr(), *p = &scr;
std::cout << scr.get() << std::endl << p->get() << std::endl;
```

在类外定义成员函数时，类名后的部分都在类的作用域中。但是函数的返回类型出现在类名之前，因此当使用函数内类型时，仍然需要注明类。

``` cpp
void Window_msg::clear(ScreenIndex i) { // ScreenIndex 处已经在类的作用域之内，不用加 Window_msg::
    Screen &s = screens[i]; // screens 也不用声明类
    s.contents = std::string(s.height * s.width, ' ');
}

Window_msg::ScreenIndex // 类型在类名之前，因此仍然需要注明类名
Window_msg::addScreen(const Screen &s) {
    screens.push_back(s);
    return screens.size() - 1;
}
```

# 类的名字查找

编译器会先处理完类中所有的名字声明，然后再处理类内函数体的定义（注意，非函数体的部分仍然要提前声明）。

## 成员函数的名字查找

- 首先在成员函数的作用域中找
- 再在整个类中找
- 最后在文件中**成员函数定义之前**的范围找

## 类型的定义

如果类的外层作用域定义了某个类型，且类中某个成员已经使用了这个类型，则该类型不能在类内再次定义。因此类型名通常定义在类的开始处，以此保证所有的成员定义都在类型定义之后。

``` cpp
using Money = int;
class X {
    Money a;
    using Money = double; // 错误
};
```

定义在外层的成员函数要注意类型名的作用域范围。

``` cpp
using Type = std::string;
class X {
    using Type = int;
    Type val = 0; // int
    Type setVal(Type i); // int, int
};

Type X::setVal(Type i) { val = i; } // std::string, int 非法
X::Type X::setVal(Type i) { val = i; } // int, int 合法
```

## 访问全局变量

可以用 `::var` 来访问全局变量

# 构造函数

## 构造函数的初始值列表

注意"初始化"和"赋值"是两个不同的概念。先执行初始化列表，再执行构造函数函数体。

没有在初始化列表中显式初始化的成员，会采用默认初始化。（即使后续进行赋值，因此使用初始值列表开销更小）

### 必须初始化的成员

未提供默认构造函数的类类型成员、引用和 `const` 成员必须要初始化，而不能在构造函数中赋值。可以直接在定义的时候初始化，也可以通过构造函数的初始化列表初始化，但是不能通过构造函数赋值。

``` cpp
class ConstRef {
    ConstRef():i(1), j(i) {} // 合法
    ConstRef() { // 非法
        i = 1;
        j = i;
    }
    const int i; // const int i = 1; 也合法
    int &j; // int &j = i; 也合法
}
```

### 成员初始化顺序

成员初始化的顺序与它们在类中定义的顺序相同，与构造函数初始化列表的顺序无关（最好采用成员声明的顺序赋初始值）。

``` cpp
class X {
    int i; int j;
    X(int ival):j(ival), i(j) {} // 非法
}
```

### 构造函数的默认实参

当为一个构造函数的所有参数都提供了默认实参时，这个构造函数可以看做是一个默认构造函数。但是不能所有的函数都这么做。

## 委托构造函数

即构造函数调用另一个构造函数完成初始化的过程。

用了委托构造函数就不能再用初始化列表。

``` cpp
class Sales_data {
public:
    Sales_data(std::string s, unsigned cnt, double price): bookNo(s), units_sold(cnt), revenue(price*cnt) {}
    Sales_data(): Sales_data("", 0, 0) {} // 委托构造函数
    Sales_data(std::istream &is): Sales_data() { read(is, *this); } // 先委托，再操作
}
```

## 默认构造函数

对象在默认初始化和值初始化时都会执行默认构造函数。

- 默认初始化
  - 不使用初始值定义的非 `static` 变量或数组
  - 类类型的成员使用合成的默认构造函数
  - 类类型的成员没有在构造函数初始值列表中初始化
- 值初始化
  - 数组定义中提供的初始值少于其大小（内置类型补 `0`）
  - 不使用初始值定义 `static` 变量（默认为 `0`）
  - 使用 `T()` 显式请求初始化

类必须包含默认构造函数在这些情况中使用，并且要注意为所有的成员都提供初始化。

使用默认构造函数的时候**不能加括号**。如 `Sales_data obj` 与 `Sales_data obj()`（后者为函数定义）

## 隐式类类型转换

如果构造函数只接受一个实参，那么它就变成了**转换构造函数**，并定义了一条转换规则。

``` cpp
struct S {
    int a, b;
    S(): S(0) {}
    S(int ival): a(ival), b(ival) {}

    void add1(S &rhs) { this->a += rhs.a; this-> += rhs.b; }
    void add2(const S &rhs) { this->a += rhs.a; this-> += rhs.b; }
} st = 1; // st(1)
```

但是编译器只会执行一步类型转换。如构造函数接受 `std::string`，那就不能直接传字面值，要先转换成 `std::string`。

``` cpp
item.combine(std::string("9-999-99999-9")); // std::string 隐式转换为 Sales_data
item.combine(Sales_data("9-999-99999-9")); // const char* 隐式转换为 std::string
```

转换的中间量是个临时量，在使用完后会被丢弃。因此不能在非 `const` 的引用上进行隐式类型转换。

``` cpp
st.add1(2); // 非法，无法进行类型转换
st.add2(2); // 合法
```

### `explicit`

可以在构造函数前用 `explicit` 修饰来防止用于类型转换。`explicit` 只需要在声明处使用，在定义处不能重复。

``` cpp
struct S {
    S(): S(0) {}
    explicit S(int ival): a(ival) {}
    int a;
} st = 1; // 非法
```

使用了 `explicit` 的函数也不能使用拷贝初始化，但是 `explicit` 函数仍然可以用来显式转换。

``` cpp
S st3 = 1; // 非法

S st3 = S(1); // 合法
S st2 = static_cast<S> (1); // 合法
```

## 聚合类

有以下特性的类被称为**聚合类**:

- 所有成员都是 `public` 的
- 没有构造函数或类内初始值
- 没有 `Base` 类，没有 `virtual` 函数

``` cpp
struct Data {
    int ival;
    std::string s
} d;
```

聚合类可以直接用花括号初始化（如 `d = {0, "abc"};`），赋值的顺序必须和变量的顺序一致。

而且如果只提供了一部分元素，那么后面的元素会值初始化。

## 字面值常量类

字面值常量类分为两种：聚合类 和 满足以下要求的非聚合类：

- 数据成员都是字面值类型
- 类至少有一个 `constexpr` 构造函数
- 如果有类内初始值，必须是常量表达式；如果有类类型的成员，初始值必须用它的 `constexpr` 构造函数
- 必须用析构函数的默认定义

字面值常量可用于 constexpr，这意味着可以在编译期确定

### `constexpr` 构造函数

`constexpr` 构造函数可以声明成 `=default` 或者 `=delete` 的形式，或者满足 `constexpr` 函数的构造函数。因此 `constexpr` 构造函数的函数体一般是**空的**。

`constexpr` 函数必须初始化所有成员。

``` cpp
class S {
public:
    constexpr S() = default;
    constexpr S(int i): a(i) {}
private:
    int a = 0;
};
```

`constexpr` 构造函数可以用来生成 `constexpr` 对象或者 `constexpr` 函数的参数或返回值。

# 类的 `static` 成员

类的 `static` 成员与具体的对象无关，属于类本身。

`static` 成员函数不和对象绑定，不包含 `this` 指针，因此不能声明为 `const` 成员函数。因为没有 `this` 指针，`static` 成员函数只能访问 `static` 成员变量（访问其它对象隐式调用了 `this` 指针）。

``` cpp
class S {
public:
    static void test1() { return stv; } // 合法
    static void test2() { return v; } // 非法
    int v = 1;
    static constexpr stv = 2;
};
```

使用类的 `static` 成员可以用 `.`、`->`，也可以用 `::` 访问。

``` cpp
Account ac1;
Account *ac2 = &ac1;
double r;
r = ac1.rate();
r = ar2->rate();
r = Account::rate();
```

## static 成员变量定义

`static` 成员函数定义在类外部的时候，只要声明时加 `static` 修饰，定义时不能重复修饰。

因为 `static` 成员不属于任何对象，所以它不是对象初始化时定义的，不能在类内初始化 `static` 对象。`static` 成员的定义和初始化在类之外，必须在全局作用域中定义，生命周期存在于整个程序。(`private static` 也可在类外直接定义）

``` cpp
double Account::interestRate = initRate(); // interestRate 是一个 static 成员，initRate 是一个类内 static 成员函数
```

同样，从类名开始，剩余部分的作用都在类中。因此定义时可以用 `private` 修饰的函数。

一般将 `static` 变量在 `cpp` 文件中定义，防止重复定义。

## `static` 成员变量的类内初始化

`static` 对象如果要在类内初始化要满足几个条件：

- 初始值必须是常量表达式
- 初始值必须是 `const` 的整型（`int`, `char` 之类），或 `constexpr` 的字面值类型

一般类内定义用于简单的几个场景（定义数组维度等，类在编译阶段要确定占用空间）。此时在类外不能再提供初始值，不过通常会在类外定义一遍。（如果编译器可以将变量全部替换为常量则不需要类外定义，否则需要类外定义，如有引用指向 `static` 变量时不能优化，必须类外定义）

``` cpp
class S {
    static const int a = 1; // 合法
    static const double b = 1; // 非法
    static constexpr double c = 1; // 合法
    int arr[a];
};
```

反过来，`constexpr` 成员必须是 `static` 的（因为编译器已经确定，不会在每个成员中定义）

`static` 对象一般不类内初始化是因为，如果类内初始化，每个对象初始化时都会进行 `static` 对象初始化，而实际上 `static` 变量在对象生成前就已经存在；但如果是 `constexpr` 则可以在编译器被替换。

## `static` 成员的应用

静态对象在某些非静态对象不能用地方会有用途，如：

- 定义不完全类型成员，即包含自身的成员
- 静态成员也可以作默认实参（可编译阶段确定）

``` cpp
class S {
    static S mem; // 包含自身的成员

    static int i;
    int j;
    S clear(int ival=i) { j=ival; } // 作默认实参
};
```
