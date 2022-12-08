---
layout: "post"
title: "「C++ Primer」 18 Tools for Large Programs"
subtitle: "异常处理、命名空间、多重继承与虚继承"
author: "roife"
date: 2020-08-18

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 异常处理

异常处理时，会跳过 `throw` 后面的代码，并沿着调用链跳到相应的 `catch` 语句。

## 抛出异常

- **析构函数**不应该抛出异常，即使有异常也必须放在 `try` 内（否则位于异常之后的代码会无法正常释放资源）
- `throw` 不应该抛出局部对象的指针（因为一般已经被销毁了）
- 对于类对象：
  + `throw` 抛出的必须是完全类型（即类对象必须有定义，不能只有声明）
  + `throw` 抛出的表达式的类型是静态类型，所以如果抛出一个基类指针，将无法发生动态绑定

### 栈展开

用 `throw` 抛出异常时，按照栈展开的顺序寻找 `catch` 语句：

- 如果语句在 `try` 块中，则寻找对应的 `catch` 语句
  - 如果找到了，执行 `catch` 语句，然后跳到该 `try` 语句对应的最后一个 `catch` 之后的语句
- 如果没找到：
  - 如果当前的 `try` 语句嵌套在其它 `try` 语句中，则跳到外层的 `try` 语句，并执行第一步
  - 如果当前的 `try` 语句没有嵌套，则结束函数，跳到外层函数寻找 `try` 语句，并执行第一步
- 如果始终没有找到，则调用 `std::terminate()`（负责退出程序）

栈展开的过程中，跳出语句块时，局部变量会自动销毁。

## 捕获异常

`catch` 语句可以忽略捕获的形参。

捕获的对象必须是完全类型。可以是左值引用，但是不能是右值引用。如果绑定了基类对象，并且传入派生类对象，那么多余部分会被丢掉。
如果是基类对象的引用，那么也无法使用派生类对象的成员（因为无法发生动态绑定）。

### 匹配 `catch`

匹配 `catch` 时会从上到下按照顺序匹配，所以特殊的 `catch` 应该放到列表的最前端（如派生类异常的处理要放在基类前端）。

- 非 `const` 对象可以匹配 `const` 和 `const T&`
- 允许将数组转换为指针
- 其它转换（如算术类型转换和类类型转换）都不能进行匹配

### 重新抛出

一个单独的 `catch` 语句无法处理异常时，可以直接用空 `throw` 将异常重新抛出给后面的 `catch` 处理。

空 `throw` 必须出现在 `catch` 中或间接包含在 `catch` 中，否则将直接调用 `std::terminate()`
终止程序。

如果在 `catch` 中改变了参数，只有当参数为引用类型时，修改的内容才会被保留。

``` cpp
catch (my_error &eObj) {
    eObj.status = errCodes::severeErr;
    throw; // 新的对象
} catch (other_error eObj) {
    eObj.status = errCodes::badErr;
    throw; // 旧的对象
}
```

### 捕获所有异常

用 `catch(...)` 可以捕获所有异常，一般放在异常的前面位置配合 `throw;` 使用（如果所有异常都被前面捕获了，`catch(...)` 放在最后就没意义了）。

``` cpp
try {

} catch (...) {

}
```

## 构造函数异常（函数测试块）

构造函数初始化列表的异常无法用函数体内的 `try` 捕获（因为此时函数体不存在），必须用**函数测试块**。

函数测试块可以处理初始化列表和函数体内发生的异常，但是无法处理初始化构造函数参数时发生的异常（此时认为是调用者去处理）。

``` cpp
template <typename T>
Blob<T>::Blob(std::initializer_list<T> il) try :
    data(std::make_shared<std::vector<T>>(il)) {
        // ...
    } catch(const std::bad_alloc &e) {
    handle_out_of_memory(e);
}
```

## `noexcept`

用 `noexcept` 或者 `throw()` 指定的函数不会抛出异常，有利于编译器优化。

如果声明了 `noexcept` 还抛出异常，会直接用 `std::terminate()` 终止程序。

``` cpp
void recoup(int) noexcept;
void recoup(int) throw();
```

### `noexcept` 使用

- 函数的声明和定义都必须使用 `noexcept`
- 函数指针的声明和定义中可以指明 `noexcept`
- `typedef` 和 `using` 作类型别名时不能出现 `noexcept`
- `noexcept` 应该出现在 `const` 和引用限定符之后，在 `final`, `override` 和纯虚函数的 `=0` 之前

### `noexcept` 说明符

用 `true` 表示不会抛出异常，用 `false` 表示可能会抛出异常。

``` cpp
void recoup(int) noexcept(true);
void recoup(int) noexcept(false);
```

### `noexcept` 运算符

`noexcept` 运算符和 `sizeof` 类似，其返回一个 `bool` 常量右值表达式，并且不会对参数求值。

当参数不可能抛出异常（当其本身不包含 `throw` 且调用的函数都是 `noexcept`）时，返回 `true`。

``` cpp
noexcept(recoup(i));
```

可以利用 `noexcept` 运算符和说明符使得函数异常说明一致。

``` cpp
void f() noexcept(noexcept(g())); // 令 f() 和 g() 的异常说明一致。
```

### `noexcept` 与虚函数/指针/拷贝控制

普通函数指针可以指向 `noexcept` 函数，`noexcept` 函数指针只能指向 `noexcept` 函数。

``` cpp
void (*pf1) (int) noexcept = recoup;
void (*pf2) (int) = recoup;
```

`Base` 的虚函数用 `noexcept` 声明，则重载时 `Derived` 中的该函数也必须用 `noexcept` 声明。反之 `Derived` 可以用 `noexcept` 声明 `Base` 中非 `noexcept` 的虚函数。

``` cpp
class Base {
public:
    virtual double f1(double) noexcept;
    virtual int f2() noexcept(false);
    virtual void f3();
};

class Derived : public Base {
public:
    double f1(double);
    int f2() noexcept(flase);
    void f3() noexcept;
};
```

如果所有的成员函数（包括 `Base` 和 `Derived`）都用 `noexcept` 声明，则合成的函数默认为 `noexcept`。

编译器会自动为析构函数提供异常声明，规则同上。

## 异常类层次

- `std::exception`：仅定义了拷贝构造函数，拷贝赋值运算符，虚析构函数和 `what()` 虚成员（返回 `const char*`，保证不抛出异常）
  - `std::bad_cast`
  - `std::bad_alloc`
  - `std::runtime_error`：无默认构造函数，有一个接受 `std::string` 或字符数组的构造函数
    - `std::overflow_error`
    - `std::underflow_error`
    - `std::range_error`
  - `std::logic_error`：无默认构造函数，有一个接受 `std::string` 或字符数组的构造函数
    - `std::domain_error`
    - `std::invalid_argument`
    - `std::out_of_range`
    - `std::length_error`

### 自定义 `std::exception` 类

``` cpp
class out_of_stock : public std::runtime_error {
public:
    explicit out_of_stock(const std::string &s):
        std::runtime_error(s) {}
};
```

# 命名空间

命名空间可以避免名字冲突。

## 命名空间定义

命名作用域包含关键字 `namespace` 名字和主体，结尾不需要分号。

命名空间内可以包含所有允许出现在**全局作用域**中的名字（类、变量、函数、模板、其它命名空间）。
命名空间可以定义在全局作用域或嵌套定义，但是不可以被定义在其它函数和类的内部，所以**命名空间可以看做特殊的全局作用域**。

``` cpp
namespace cplusplus_primer {
    class xxx {};
} // 不需要分号
```

每个命名空间都是一个作用域。命名空间内的成员可以直接被该命名空间的**其它成员**访问，也可以直接被**内层作用域**的成员访问（外层访问内层要用 `::`）。

``` cpp
cplusplus_primer::Query q = cplusplus_primer::Query("hello");
```

### 命名空间定义可以不连续

``` cpp
// a.cpp
namespace std {

}

// b.cpp
namespace std {

}
```

因此可以用几个独立的文件组成一个命名空间，一部分文件用来声明（放在头文件），一部分实现定义。

虽然可以分开定义，但是相同命名空间的名字不可以重复。

### 外部命名空间成员

类似于类，看到命名空间的前缀后，剩余部分都包含在命名空间中。

``` cpp
cplusplus_primer::Sales_data
cplusplus_primer::operator+(const Sales_data &lhs, const Sales_data &rhs) {}
```

定义外部成员时，必须在该类的外层空间中定义，不能在与之并列的命名空间中定义。

### 模板特例化

特例化模板必须定义在原始模板的命名空间中。可以在内部声明，外部定义。

``` cpp
namespace std {
    template <> struct hash<Sales_data>;
}

template <>
struct std::hash<Sales_data> {
    // ...
}
```

### 全局命名空间

用 `::member` 访问。

### 嵌套命名空间

嵌套命名空间类似于嵌套作用域，内层不可以访问外层的名字。

``` cpp
namespace A {
    namespace B {

    }
}
```

访问的时候用 `A::B::member`。

### `inline` 命名空间

内联命名空间（在 `namespace` 前加 `inline`）的名字可以直接被外层使用。

`inline` 必须加在第一次定义命名空间的地方，后面再次打开可以不加。

``` cpp
inline namespace FifthEd {

}

namespace FifthEd { // 隐式 inline

}
```

当代码有多个版本时，可以在最新版的代码上用内联命名空间简化调用。（这个新版代码就可以直接用 `mem` 调用，旧版则需要用 `last_ver::mem` 调用）

### 未命名的命名空间

未命名的命名空间即定义时省略名字。

``` cpp
namespace {

}
```

未命名的命名空间中定义的成员具有**静态生命期**，即第一次定义时被创建，程序结束时被销毁。

未命名的命名空间也可以不连续，但是每个文件的未命名命名空间是**独立**的（名字不共享）。因此如果在头文件定义未命名命名空间，则会在每个程序文件中生成不同的主体。

未命名命名空间的名字可以直接被外层使用，并且不能和命名空间所处作用域内的名字冲突。

``` cpp
int i;

namespace {
    int i; // 非法，二义性
}

namespace local {
    namespace {
        int i;
    }
}

local::i = 42; // 直接在外层使用，合法
```

## 使用命名空间成员

### 命名空间别名

用 `namespace A = B` 可以设置命名空间别名。

``` cpp
namespace primer = cplusplus_primer;
```

### `using`

`using` 有两种用法：

- `using` declaration：`using xxx`，一次只引入一个成员。在类的作用域中使用时，只能指向 `Base` 的成员
- `using` directive：`using namespace xxx`，不能用于类的作用域中

在局部作用域中使用 `using` directive 等价于将 `namespace` 的代码放到最近的全局作用域中。

``` cpp
namespace blip {
    int i = 16, j = 15, k = 23;
}

int j = 0;

void manip() {
    using namespace blip;

    ++i; // blip::i
    ++j; // 二义性错误
    ++::j; // 全局的 j
    ++blip::j; // blip::j
    int k = 97; // 隐藏了 blip::k
}
```

由于 `using` directive 具有污染性，因此头文件中一般不使用它。

## 类与命名空间

命名空间的名字查找过程和作用域的一样，从内到外，且只考虑调用点之前的名字。

在命名空间中的类和在外部的一样，先在类内查找，再到外部作用域查找。同样，只考虑调用点之前的名字。

``` cpp
namespace A {
    int i, j;

    class C {
    public:
        int f0() { return i; } // 正确，返回 A::i
        int f1() { return j; } // 正确，返回 C::j，外层名字被隐藏
        int f2() { return k; } // 错误，找不到名字
        int f3();

    private:
        int j;
    };

    int k;
}

int A::C::f3() { return k; } // 正确，返回 A::k, f3() 定义在 A::k 之后
```

### 类类型作为实参时的特殊规则

给函数传递一个类类型的参数（或指针，引用）时，不仅会进行常规的作用域查找，还会查找这个类类型所在的命名空间。因此使用运算符，如 `std::cout << s` 时，不需要额外引入 `std::operator>>(std::cin, s);`。

### 友元与名字查找

一般类内友元声明不会使得友元可见。

类的友元默认为最近的命名空间的成员，当这个友元的参数为类类型时，结合特殊规则，可以让友元函数直接被调用。

``` cpp
namespace A {
    class C {
        friend void f2();
        friend void f(const C&);
    };
    // f2() 与 f(const C&) 的定义，可以定义在其他文件中
}

int main() {
    A::C obj;
    f(obj); // 直接调用合法，因为会到上层作用域找
    f2(); // 不合法，找不到名字
}
```

### `std::move` 与 `std::forward`

`std::move` 与 `std::forward` 接受右值引用，因此可以接受所有类型的参数，导致当自定义了同名函数时，一定会发生冲突。因此推荐加上 `std::` 避免冲突。

## 重载与命名空间

以下三者都会影响重载：

- 类类型作实参
- `using` declarations
- `using` directive

注意 `using` declaration 允许重载部分函数。但是如果在引入时，当前作用域存在同名同形参列表的函数，就会发生错误（`using` directive 不会，因为它是将名字放到作用域外）。

# 多重继承与虚继承

多重继承即从多个 `Base` 产生 `Derived`。

## 多重继承

多重继承的规则和普通继承一样，但是类派生列表中每个 `Base` 只能出现一次。

``` cpp
class Panda : public Bear, public Endangered {};
```

### 初始化

多重继承的构造函数只能初始化直接基类，构造顺序与类派生列表中出现的顺序一致（与委托的顺序无关）。

析构函数的调用顺序和构造函数恰好相反。

### 继承的构造函数

C++ 11 中允许继承构造函数（复用基类的构造函数）。在多重继承中，如果继承的两个构造函数形参列表完全相同（默认构造函数除外），就会发生错误。

此时需要自定义一个该形参列表的构造函数。

``` cpp
struct Base1 {
    Base1() = default;
    Base1(const std::string&);
    Base1(std::shared_ptr<int>);
};

struct Base2 {
    Base2() = default;
    Base2(const std::string&);
    Base2(int);
};

struct Derived: public Base1, public Base2 {
    using Base1::Base1;
    using Base2::Base2;

    // 两个继承的构造函数都包括了 const std::string& 的构造函数，需要重新定义
    Derived(const std::string&);
    Derived() = default; // 因为自定义了一个构造函数，所以也必须同时定义默认构造函数（不是因为多重继承）
};
```

### 拷贝控制

派生类使用合成版本的拷贝控制函数时，会按照类派生列表的顺序自动调用基类的拷贝控制函数。否则需要手动调用。

## 类型转换

`Derived` 的引用或指针也可以转换为某个 `Base` 的引用或指针。

编译器认为这种类型转换都是等价的，如果冲突了就会产生二义性。

``` cpp
void print(const Base1&);
void print(const Base2&);

print(Derived()); // 二义性错误
```

同样，指针或引用的静态类型决定了能够使用的名字。

## 类作用域

多重继承中名字查找将会在所有的直接基类中同时进行，如果一个名字在多个直接基类的子树中都能被找到，调用就会产生二义性。此时需要调用者明确指出使用的版本。

调用时先进行名字查找，再进行类型检查。因此两个函数如果名字相同但是形参列表不同，也会发生二义性错误。

名字查找不会考虑访问控制的限制，所以如果某个名字在 `Base1` 中为 `private`，在 `Base2` 中为 `public` 或 `protected` 也会发生错误。

为了避免这些情况，通常会在 `Derived` 定义一个新的同名函数避免冲突。或者在调用时指出所用的成员，如 `d.Base1::print()`。

``` cpp
void foo(double cval)
{
    int dval;
    dval = Base1::dval + Derived::dval;
    Base2::fval = dvec.back();
    Derived::sval[0] = Base1::cval;
}
```

## 虚继承

多重继承中，一个 `Base` 可能会被多次继承。如 `B->D1`、`B->D2`、`D1 & D2 -> DD`。此时 `Derived` 会包含多个父对象。

如果希望只包含一份父对象，可以在类派生列表中用 `virtual` 修饰 `B`，即**虚继承**。使用虚继承的基类 `B` 被称为**虚基类**。

无论是不是虚继承，都可以发生 `Derived` 向 `Base` 的转换。

### 定义虚基类

虚基类的定义必须在直接基类中（`D1` 与 `D2`）完成。

``` cpp
class D1 : public virtual B {};
class D2 : virtual public B {}; // virtual 与访问控制符的顺序随意

class DD : public D1, public D2 {};
```

### 成员可见性

虚继承不会发生多次继承同一个类的情况，因此调用不会产生二义性。

假设 `B->D1`，`B->D2`，`D1 & D2 -> DD`。如果要访问 `mem`，有几种情况：

- `mem` 只在 `B` 中出现，则不会产生二义性
- `mem` 在 `B` 和 `D2` 中出现，则优先使用更近的 `D2`，不会产生二义性
- `mem` 同时在 `D1` 与 `D2` 中出现，存在二义性错误

如果不采用虚继承，并且需要访问到 `mem`，可以用 `d.D1::mem` 和 `d.D2::mem` 访问。

### 构造函数

虚继承由最低端的派生类来进行初始化。如 `B->D1`, `B->D2`, `D1 & D2 -> DD` 中，由 `DD` 初始化 `B`（防止重复初始化）。

``` cpp
class DD : public D1, public D2 {
    DD() : D1(), D2(), B() {}
};
```

虚基类一般先于非虚基类进行初始化。

构造顺序按照类派生列表从左到右 DFS 初始化，优先初始化虚基类，然后从头开始初始化其他类，析构相反（从右到左）。合成的拷贝和移动操作的顺序与构造函数相同。

``` cpp
// 一个例子
class Character { /*...*/ };
class BookCharacter : public Character { /*...*/ };

class Bear { /*...*/ };

class ToyAnimal { /*...*/ };

class TeddyBear : public BookCharacter, public Bear, public virtual ToyAnimal { /*...*/ };

// ZooAnimal();
// ToyAnimal();
// Character();
// BookCharacter();
// Bear();
// TeddyBear();
```
