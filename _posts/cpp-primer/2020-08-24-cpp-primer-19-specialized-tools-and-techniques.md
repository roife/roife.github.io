---
layout: "post"
title: "「C++ Primer」 19 Specialized Tools and Techniques"
subtitle: "内存分配、RTTI、枚举类型、嵌套类、内部类等"
author: "roife"
date: 2020-08-24

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 控制内存分配

使用 `new` 时实际上执行了三个操作：

- 调用 `operator new` 分配空间
- 运行构造函数
- 返回指针

使用 `delete` 时实际上是执行了两个操作：

- 执行析构函数
- 调用 `operator delete` 释放空间

使用 `new` 和 `delete` 是编译器会首先在类成员中找重载的 `new` 和 `delete`，然后在全局作用域查找，最后在标准库中找。（用 `::new` 和 `::delete` 可以强制在全局作用域找）

## `operator new` 和 `operator delete`

标准库定义了 `8` 个重载版本的 `operator new` 和 `operator delete`，前四个版本可以抛出 `std::bad_alloc` 异常。

``` cpp
void *operator new(size_t);
void *operator new[](size_t); // 针对数组
void operator delete(void*) noexcept;
void operator delete[](void*) noexcept;

// 不抛出异常的版本
void *operator new(size_t, std::nothrow_t&) noexcept;
void *operator new[](size_t, std::nothrow_t&) noexcept;
void operator delete(void*, std::nothrow_t&) noexcept;
void operator delete[](void*, std::nothrow_t&) noexcept;
```

- `delete` 一般不会抛出异常
- `std::nothrow_t` 类型：定义在头文件 `new` 中的一个 `struct`
- `std::nothrow`：`const std::nothrow_t` 对象，定义在头文件 `new` 中，可以用作 `new` 和 `delete` 的参数从而调用不抛出异常的版本

声明在类中时，`operator new` 和 `operator delete` 默认是 `static` 的，而且不能操控类的成员（因为它们的调用发生在类构造之前和析构之后）。

- `operator new` 的第一个参数必须是 `size_t` 类型而且不能有默认参数。用 placement new 的形式可以给 `operator new` 传入额外实参，但是不能重载这个函数：

``` cpp
void *operator new(size_t, void*); // 被标准库用了
```

- 使用 `operator delete` 时也可以提供一个额外的 `size_t` 参数，初始值为第一个 `void*` 形参指向对象的大小。当基类有一个虚析构函数时，传入的 `size_t` 由动态类型的大小决定。

## `malloc` 和 `free`

`malloc` 和 `free` 定义在头文件 `cstdlib` 中。

- `malloc(size_t)`：接受一个 `size_t` 的参数表示分配的空间大小，返回分配空间的指针（返回 `0` 时表示分配失败）
- `free(void*)`：接受一个指向对象的指针释放内存（`free(0)` 无效果）

可以用 `malloc` 和 `free` 编写 `operator new` 和 `operator delete`。

``` cpp
void *operator new(size_t size) {
    if(void *mem = malloc(size)) {
        return mem;
    } else {
        throw std::bad_alloc;
    }
}

void operator delete(void *mem) noexcept { free(mem); }
```

## placement new

placement new 有四种形式：

``` cpp
new (place_address) type;
new (place_address) type (initializers);
new (place_address) type [size];
new (place_address) type [size] {braced_initializer_list};
```

指定 `place_address` 时会调用 `operator new(size_t, void*)` 的版本，此时不分配空间，
直接在指定的地址上构造对象（不要求地址是堆）。

## 显式调用析构函数

用于直接清除对象但是不会释放空间，可以重新使用这部分空间。

``` cpp
std::string *sp = new std::string("test");
sp->~string(); // 析构对象
```

# RTTI

- `typeid`：返回表达式类型
- `dynamic_cast`：将 `Base` 的指针和引用转换为 `Derived` 的指针和引用

RTTI 一般用于用 `Base` 的指针或引用访问 `Derived` 的某个非虚函数（注意这个指针的动态类型必须是 `Devied`）。

## `dynamic_cast`

`dynamic_cast` 有三种使用形式：

- `dynamic_cast<type*>(e)`：`e` 必须是指针，转换失败时返回 `0`
- `dynamic_cast<type&>(e)`：`e` 必须是左值，转换失败时抛出 `std::bad_cast` 异常（定义在头文件 `typeinfo` 中）
- `dynamic_cast<type&&>(e)`：`e` 不能是左值，转换失败时抛出 `std::bad_cast` 异常

其中 `type` 必须是类类型，且含有一个虚函数。

`e` 必须是以下三种情况之一：

- `e` 的类型是 `type` 的公有 `Derived` 类
- `e` 的类型是 `type` 的公有 `Base` 类
- `e` 的类型是 `type`

### 指针与 `dynamic_cast`

对 `nullptr` 执行 `dynamic_cast` 会返回目标类型的空指针。

``` cpp
if (Derived *dp = dynamic_cast<Derived*>(bp)) {
    // 使用 dp 的 Derived 对象
} else { // bp 指向 Base 对象
    // 使用 bp 的 Base 对象
}
```

### 引用与 `dynamic_cast`

``` cpp
try {
    const Derived &d = dynamic_cast<const Derived&>(b);
    // 使用 b 引用的 Derived 对象
} catch (std::bad_cast) {
    // 处理类型转换失败的情况
}
```

## `typeid`

`typeid` 表达式的形式为 `typeid(e)`，返回一个常量对象的引用，其类型为 `std::type_info` 或其派生类型，定义在头文件 `typeinfo` 中。

- 作用于 `const` 对象时，顶层 `const` 会被忽略
- 作用于引用时，返回所引用对象的类型
- 作用于**数组**或**函数**时，返回数组或函数的类型（而非指针）
- 作用于**非类类型**或**没有定义虚函数的类类型**时，返回静态类型（此时 `e` 可以为空指针）; 作用于**定义了虚函数的类的左值**时，返回动态类型（运行时计算，此时 `e` 不得为空，否则会抛出异常 `std::bad_typeid`)

`typeid` 运算符常用于比较表达式类型是否相同：

``` cpp
Derived *dp = new Derived;
Base *bp = dp;

if (typeid(*bp) == typeid(*dp)) { // 注意要取引用
    // ...
}
```

## 使用 RTTI 判断继承对象相等

当需要判断两个 `Derived` 对象是否相等时可以用 RTTI。

对于比较继承对象（即两个 `Base*` 或 `Base&`）是否相等的一个思路是定义一套虚函数，并在每个继承对象上进行重载。然而虚函数的形参列表必须统一（即都是 `Base&`），所以无法访问 `Derived` 部分的对象，此时可以用 `dynamic_cast`。

``` cpp
class Base {
    friend bool operator==(const Base&, const Base&);
public:

protected:
    virtual bool equal(const Base&);
};

class Derived : public Base {
    public:

    protected:
    virtual bool equal(const Base&) const;
};

bool operator==(const Base& lhs, const Base& rhs) {
    return (typeid(lhs) == typeid(rhs)) && lhs.equal(rhs);
}

bool Base::equal(const Base &rhs) {
    // 比较各个成员
}

bool Derived::equal(const Base &rhs) {
    auto r = dynamic_cast<const Derived&>(rhs);
    // 比较各个成员，可以采用委托的形式
    return this->Base::equal(r); // 比较 Base 的部分
}
```

## `std::type_info` 类

`std::type_info` 类定义在 `typeinfo` 头文件中，通常作为一个基类，额外的类型信息会被保存到 `Derived` 中。

`std::type_info` 没有默认构造函数，且拷贝和移动函数被定义为 `delete`。因此无法拷贝和赋值 `std::type_info` 成员，只能使用 `typeid` 运算符创建。

| 操作                   | 作用                                                          |
| ---------------------- | ------------------------------------------------------------- |
| `t1 =` t2=, `t1 != t2` | 比较两个 `std::type_info` 对象                                |
| `t.name()`             | 返回 C 风格字符串，表示类型的可打印形式（机器相关）           |
| `t1.before(t2)`        | 返回 `bool` 表示类型的顺序（机器相关，纯粹为了将类型放入容器）|

# `enum`

枚举类型属于字面值常量，分为限定作用域的枚举类型和不限定作用域的枚举类型。

- 限定作用域的枚举类型：`enum class <name> { members };` 或 `enum struct <name> { members };`，枚举类型成员的作用域遵循作用域规则
- 不限定作用域的枚举类型：`enum <name> { members };` 或 `enum { members };`（未命名的枚举类型，只能在定义时使用对象），枚举类型的作用域与枚举类型本身相同

## 枚举成员

``` cpp
enum color { red, yellow, green };
color eyes = green; // 正确
color hair = color::red; // 正确
enum color2 { red, yellow, green }; // 错误，重复定义

enum class peppers { red, yellow, green }; // 正确，变量名隐藏
peppers p = green; // 错误，green 不在作用域内
peppers p2 = peppers::green; // 正确
```

## 枚举值

默认情况下，枚举值从 `0` 开始递增，也可以指定枚举值，枚举值也不一定唯一。枚举值必须是常量表达式。

``` cpp
enum class intTypes {
    charTyp = 8, shortTyp = 16, intType = 16,
    longTyp = 32, longlongTyp = 64
};

constexpr intTypes charbits = intTypes::charTyp;
```

枚举值也可以用作 `switch` 语句，非类型的模板形参或静态数据成员。

## 枚举类型与整数值

虽然枚举成员和整数对应，但是初始化枚举类型的变量不能用整数。但是不限定作用域的枚举类型反过来可以（限定作用域的枚举类型不可以）。

``` cpp
open_modes om = 2; // 错误
open_modes om2 = open_modes::input; // 正确

int i = color::red; // 不正确
int j = peppers::red; // 错误
```

同样，枚举类型用作函数参数时也不能用整数值，但是可以把不限定作用域的枚举类型传递给整数形参。

``` cpp
enum Tokens { INLINE = 128, VISUAL = 129 };
void ff(Tokens);

ff(128); // 错误
ff(INLINE); // 正确

void newf(int);
newf(INLINE);
```

## 指定 `enum` 的整数表示

虽然枚举类型是一种独立的类型，但是其本质是整数类型，可以指定其整数类型。

``` cpp
enum intValues : unsigned long long {
    charTyp = 255, shortTyp = 65535, intTyp = 65535,
    longTyp = 4294967295UL, long_longTyp = 18446744073709551615ULL
};
```

默认情况下，限定作用域的枚举类型用 `int`，不限定作用域的枚举类型使用的类型不确定，但是能保证容纳枚举值。

## 声明枚举类型

不限定作用域的枚举类型声明时必须指明成员类型，限定作用域的枚举类型默认为 `int`。声明和定义必须匹配。

``` cpp
enum intValues : unsigned long long;
enum class open_modes; // 不声明默认为 int
```

# 类成员指针

成员指针是指向类的非静态成员（和对象区别）的指针（指向静态对象的指针和普通的指针没有区别）。

初始化成员指针时只提供类的类型和对象的类型，在使用时才提供具体的对象。

## 数据成员指针

### 定义数据成员指针

声明成员指针要加上类名：`<type> <className>::*<varName> = &<className>::<member>`。

``` cpp
const std::string Screen::*pdata;
pdata = &Screen::contents;

auto pdata = &Screen::contents;

static const std::string Screen::*data() { return &Screen::contents; }
```

### 使用数据成员指针

初始化成员指针时并没有指向某个对象的数据，需要使用 `.*` 和 `->*` 解引用后使用。

``` cpp
Screen myScreen, *pScreen = &myScreen;
auto s = myScreen::*pdata;
s = pScreen->*pdata;
```

使用数据成员指针要遵循访问控制规则，只能在类内部或者友元中使用。

## 成员函数指针

### 定义成员函数指针

如果成员函数存在重载，则必须指出函数类型。

成员函数指针定义时要包含返回类型、形参列表、`const` 限定符等。最简单的方法是直接用 `auto` 指定类型。（为了方便可以用 `typedef` 或 `using`）

``` cpp
auto pmf = &Screen::get_cursor;

char (Screen::*pmf2)(Screen::pos, Screen::pos) const;
pmf2 = &Screen::get;
// get 函数原型为 char get(pos ht, pos wd) const;

using Action = char (Screen*) (Screen::pos, Screen::pos) const;
Action get = &Screen::get;
```

定义时不能省略 `::*` 两边的括号，否则会被当做函数声明。

成员函数不能当做函数指针用，必须要用 `&` 取地址。

``` cpp
pmf2 = Screen::get; // 错误
pmf2 = &Screen::get; // 正确
```

### 使用成员函数指针

用 `.*` 与 `->*` 可以使用成员函数指针。

``` cpp
Screen myScreen *pScreen = &myScreen;
char c1 = (pScreen->*pmf)();
```

函数名两端的括号不可少（优先级顺序）。

### 成员函数表

相同返回值和形参类型的函数可以放到一个数组中，通过下标调用。

``` cpp
class Screen {
public:
    using Action = Screen& (Screen::*)();

    enum Directions = { HOME, FORWARD, BACK, UP, DOWN };

    Screen& move(Directions);
  // ...

private:
    static Action menu[];
};
Screen::Action Screen::menu[] = {
                                 &Screen::home,
                                 &Screen::forward,
                                 &Screen::back,
                                 &Screen::up,
                                 &Screen::down
};

Screen& Screen::move(Directions cm) {
  return (*this->menu[cm])();
}

Screen myScreen;
myScreen.move(Screen::HOME);
```

## 成员函数指针作为可调用对象

成员函数指针不支持 `()` 运算符，不能直接存在 `std::vector` 等容器中作为可调用对象，需要封装。

### 用 `std::function` 封装

用 `sts::function` 封装成员函数指针时，必须提供函数类型，其中函数的第一个形参表示成员函数所属对象的类型，且必须指明是用指针还是用引用调用的。

``` cpp
std::vector<std::string*> pvec;
std::function<bool (const std::string*)> fp = &std::string::empty;
std::find_if(pvec.begin(), pvec.end(), fp);
```

`fp(*it)` 会转换为 `((*it).*p)`（`p` 是被封装的成员函数指针）。

### 用 `std::men_fn` 封装

使用 `std::mem_fn` 封装可以自动推断类型，而且指针和引用都可以直接调用。

``` cpp
std::find_if(svec.begin(), svec.end(), std::men_fn(&std::string::empty));

auto f = std::mem_fn(&std::string::empty);
f(svec[0]);
f(svec.begin());
```

### 用 `std::bind` 封装

使用 `std::bind` 类似于 `std::function`，必须显式绑定函数调用对象到参数（`_1`），同时和 `std::mem_fn` 一样既可以用引用也可以用指针调用。

``` cpp
auto it = std::find_if(svec.begin(), svec.end(), std::bind(&std::string::empty, std::placeholders::_1));

auto f = std::bind(&std::string::empty, std::placeholders::_1);
f(*svec.begin());
f(&svec[0]);
```

# 嵌套类

嵌套类即一个类定义在另一个类的内部，本质上是在外层类里面定义了一个**类型**。

嵌套类的名字在外层类可见，但是在外层类之外不可见。

## 声明嵌套类

在使用嵌套类前必须对其进行声明。

可以直接在外层类中声明：

``` cpp
class TextQuery {
public:
    class QueryResult;
};
```

## 定义嵌套类

嵌套类可以用 `classA::classB` 的形式定义在类的外部，在定义前属于不完全类型。

``` cpp
class TextQuery::QueryResult {
    // ...
};
```

## 定义嵌套类成员

用 `classA::classB::member` 的方式定义嵌套类成员。

``` cpp
TextQuery::QueryResult::QueryResult(std::string s,
                                    std::shared_ptr<std::set<line_no>> p,
                                    std::shared_ptr<std::vector<std::string>> f) :
    sought(s), lines(p), file(f) { }
```

## 嵌套类的静态成员

嵌套类的静态成员要定义在外层类的作用域之外。

``` cpp
int TextQuery::QueryResult::member = 1024;
```

## 嵌套类的名字查找和访问外层类

嵌套类可以在外层类进行名字查找，并且可以直接访问外层类的 `private` 对象。

外层类也可以使用嵌套类来定义对象。

## 嵌套类与外层类相互独立

嵌套类对象的和外层类对象**相互独立**，即嵌套类的对象不包含外层类对象的成员，在外层类的对象中也不包含嵌套类对象的成员。

本质上嵌套类只是定义了一种类型。

# `union`

`union` 是一种特殊的类，拥有多个成员，但是只有其中一个有值。给一个成员赋值后，其它成员的值为未定义。

分配给一个 `union` 对象的存储空间至少能容纳它最大的数据成员。

`union` 的特殊性有：

- 不能有引用类型的成员
- 可以为成员指定访问控制，默认为 `public`
- `union` 可以定义构造函数和析构函数，但是不能继承，也不能作为 `Base`，不能有虚函数

## 定义和使用 `union`

初始化可以直接用花括号，且默认初始化第一个成员。

``` cpp
union Token {
    char cval;
    int ival;
    double dval;
};

Token first_token = {'a'}; // 初始化  cval
Token *pt = new Token;
pt->ival = 42;
```

必须要明确 `union` 中存储的数据成员的类型。

## 匿名 `union`

匿名 `union` 会自动创建一个对象，并且在定义的作用域内可以直接访问其成员。

但是匿名 `union` 只能有 `public` 成员，而且不能定义成员函数。

``` cpp
union {
    char cval;
    int ival;
    double dval;
};

cval = 'c';
```

## 含有类类型的 `union`

如果 `union` 包含了拥有**默认构造函数**或**拷贝控制函数**的类类型成员，该 `union` 的对应成员会被定义为 `delete`，此时如果一个类包含了这个 `union` 这个类的对应成员也会被定义为 `delete`。

包含类类型的 `union` 的构造、赋值、析构行为必须自定义控制。

### 使用类管理 `union`

通常会用一个单独的类管理包含类类型的成员。

这个类会用枚举类型保存 `union` 中存储的值的具体类型（称为判别式），并且自定义默认构造函数和拷贝控制成员。

``` cpp
class Token {
public:
    Token() : tok(INT), ival{0} { }
    Token(const Token &t) : tok(t.tok) { copyUnion(t); }
    Token &operator=(const Token&);
    ~Token() { if (tok == STR) sval.~string(); }

    Token &operator(const std::string&);
    Token &operator(char);
    Token &operator(int);
    Token &operator(double);

private:
    enum {INT, CHAR, DBL, STR} tok; // 判别式
    union {
        char cval;
        int ival;
        double dval;
        std::string sval;
    };
    void copyUnion(const Token&);
};
```

### 给 `union` 赋值

如果当前 `union` 的值为类类型的成员时，需要手动进行销毁。

``` cpp
Token &Token::operator=(int i) {
    if (tok == STR) sval.~string();
    ival = i;
    tok = INT;
    return *this;
}
```

给 `union` 赋值一个类类型成员时，要用 placement new。

``` cpp
Token &Token::operator=(const std::string &s) {
    if (tok == STR) sval = s;
    else new(&scal) std::string(s);
    tok = STR;
    return *this;
}
```

### 用 `union` 赋值

通常定义一个辅助函数来处理赋值，且赋值时对于每种类类型的情况都要分开考虑。

``` cpp
void Token::copyUnion(const Token &t) {
    switch (t.tok) {
    case Token::INT : ival = t.ival; break;
    case Token::CHAR : cval = t.cval; break;
    case Token::DBL : dval = t.dval; break;
    case Token::STR new(&sval) string(t.sval); break;
    }
}

Token &Token::operator=(const Token &t) {
    if (tok == STR && t.tok != STR) sval.~string();
    if (tok == STR && t.tok == STR) s.val = t.sval;
    else copyUnion(t);
    tok = t.tok;
    return *this;
}
```

# 局部类

定义在函数内部的类被称为局部类，其成员受到严格限制（这点与嵌套类不同）。

- 局部类的成员必须全部定义在类的内部
- 局部类不允许声明 `static` 成员
- 局部类不能使用函数作用域中的变量（只能访问类型，`static` 变量和枚举成员）
- 外层函数访问局部类要遵循访问控制（也可以定义外侧函数为 `friend`，但是一般直接声明为 `public`）
- 局部类可以嵌套（此时嵌套类可以定义在局部类之外），并且也是一个局部类，其成员必须定义在嵌套类的内部

``` cpp
void foo {
    class Bar {
    public:
        class Nested;
    };

    class Bar::Nested {

    };
}
```

# 不可移植的特性

## 位域

位域即指定某个成员所占的二进制位数，其内存分配与内存对齐的实现方式是机器相关的。

非 `static` 的数据成员可以被定义为位域，类型必须是整型或枚举类型，一般使用无符号类型。

``` cpp
typedef unsigned int Bit;
class File {
    Bit mode: 2; // 位域的声明使用一个冒号和一个常量表达式
    Bit modified: 1;
    Bit prot_owner: 3;
    Bit prot_group: 3;
    Bit prot_world: 3;
public:
    enum modes { READ = 01, WRITE = 02, EXECUTE = 03 };
};
```

一般类内定义的连续位域会被压缩到一个整数的相邻位，从而节省空间。

`&`（取地址符）不能作用于位域。

### 操作位域

访问位域和访问其它数据成员一样。操作位域可以用位运算。

``` cpp
void File::write() {
    modified = 1;
}

File &File::open(File::modes m) {
    mode |= READ;
    if (m & WRITE) return *this;
}
```

对于位域一般会定义一些 `inline` 的小函数操作和取出位域。

``` cpp
inline bool FILE::isRead() const { return mode & READ; }
inline void FILE::setWrite() { mode |= WRITE; }
```

## `volatile`

`volatile` 修饰符用于告诉编译器不对该对象进行优化。

``` cpp
volatile int display_register;
volatile const int iax[max_size];
```

`volatile` 和 `const` 十分相似，可以有底层 volatile, `volatile` 函数等。`volatile` 指针必须指向 `volatile` 对象，`volatile` 引用必须引用自 `volatile` 对象。

``` cpp
volatile int v;
int *volatile vip;
volatile int *ivp;
volatile int *volatile vivp;

ivp = &v;
```

`volatile` 对象只能使用 `volatile` 成员函数。

### 合成的拷贝对 `volatile` 对象无用

`volatile` 不能用合成的**拷贝**、**移动**构造函数和赋值运算符来初始化 `volatile` 对象或给 `volatile` 对象赋值。因为合成的对象是 `const ClassName&`，不包含 `volatile`。

因此需要自己定义 `volatile` 对象的拷贝和赋值操作。

``` cpp
class Foo {
public:
    Foo(const volatile Foo&);
    Foo& operator=(volatile const Foo&);
    Foo& operator=(volatile const Foo&) volatile;
}
```

## `extern "C"` 链接指示

调用其它语言的函数时也需要在 C++ 中进行声明（必须保证有权访问该语言的编译器，且该编译器与当前的 C++ 编译器兼容）。

有单一和复合两种声明方式（还可以用 `extern "Ada"`，`extern "FORTRAN"` 等）,
编写函数所用的语言被认为是类型的一部分：

``` cpp
extern "C" size_t strlen(const char*);
extern "C" {
    int strcmp(const char*, const char*);
    char* strcat(char*, const char*);
}
```

链接指示不能出现在类或函数的内部，可以嵌套。

复合声明可以直接用于头文件：

``` cpp
extern "C" {
    #include <string.h>
}
```

### 指向链接函数的指针

因为编写函数所用的语言被认为是类型的一部分，所以二者的指针不能混用：

``` cpp
extern "C" void (*pf) (int);
void (*pf2) (int);
pf1 = pf2; // 错误
```

链接指示对整个声明的内容都有效。

``` cpp
extern "C" void f1(void(*)(int));
// 这个函数接受的函数指针参数也必须是 extern "C" 的
```

给 C++ 函数传入 C 的指针时，必须用类型别名。

``` cpp
extern "C" typedef void FC(int);
void f2(FC *);
```

### 导出 C++ 的函数

用 `extern` 定义的函数可以在其它语言中使用。

``` cpp
// 可以被 C 调用
extern "C" double calc(double dparm) {}
```

### `__cplusplus`

用 `__cplusplus` 宏可以包含一些只有用 C++ 时才会编译的代码。（用于 C++ 与 C 混写）

``` cpp
#ifdef __cplusplus
// 编译 C++ 程序时使用
#endif
```

### 重载函数

是否可以重载函数依赖目标语言，如 C 语言不支持重载，那么就不能导出重载的函数。
