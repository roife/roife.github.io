---
layout: "post"
title: "「C++ Primer」 15 Object-Oriented Programming"
subtitle: "面向对象"
author: "roife"
date: 2020-08-07

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# OOP 概述

## 继承的概念

Derived class（派生类，以下简称 `Derived`）通过继承得到 Base class（基类，以下简称 `Base`）的成员。其中，`Base` 中希望 `Derived` 自己定义的成员函数要声明成**虚函数**，用 `virtual` 修饰。

`Derived` 通过**类派生列表**来指出继承的 `Base`。类派生列表前可以加访问控制修饰符。

``` cpp
class Quote {
public:
    std::string isbn() const;
    virtual double net_price(std::size_t n) const; // 虚函数
};

class Bulk_quote: public Quote { // 类派生列表
public:
    double net_price(std::size_t) const override; // 重载
};
```

## 动态绑定

当函数的参数为 `Base` 的引用或指针时，通过它调用的成员函数可以是 `Base` 的，也可以是 `Derived` 的，取决于传入参数的对象。其调用的成员函数的版本在运行时进行识别，因此被称为**动态绑定**。

**只有虚函数能发生动态绑定。**

``` cpp
double print_total(ostream &os, const Quote &item, size_t n) {
    double ret = item.net_price(n); // item 既可以是 Quote 也可以是 Bulk_quote，使用哪个版本的 net_price() 由参数类型决定
    os << "ISBN: " << item.isbn()
       << " # sold: " << n << " total due: " << ret << endl;
    return ret;
}
```

# 基类与派生类

## `Base`

`Base` 通常会定义一个 `virtual` 析构函数，因为 `Derived` 中往往有自己独有的对象，需要通过自己的析构函数进行释放。

### `Base` 中的虚函数

`Base` 中希望 `Derived` 重新覆盖的函数被定义为**虚函数**，使用指针或引用调用时会根据对象类型发生**动态绑定**。

**非虚函数在编译期发生解析，虚函数在运行时进行解析。**

- 只有构造函数和 `static` 函数不能成为虚函数
- `virtual` 只能在类内部声明时使用，**不能出现在类外部的定义**
- `Base` 中的虚函数必须有定义！（否则就是纯虚函数了）

### 访问控制与继承

`Derived`：
- 可以访问 `public` 和 `protected`
- 不能访问 `private`。用户可以访问 `public`
- 不能访问 `protected` 和 `private`

## `Derived`

类派生列表可以用**访问控制修饰符**（`public`、`private`、`protected`）来修饰 `Base`，用来控制继承的对象是否对 `Derived` 可见。如果用 `public` 来修饰派生关系，那么 `Derived` 可以访问 `Base` 的 `public` 成员。

可以把 `Derived` 的对象绑定到 `Base` 的引用或指针上（动态绑定）。

``` cpp
class A {};
class B: public A{};
B b;
A &refa = b; // 合法
```

### `Derived` 中的虚函数

`Derived` 通常会覆盖继承的虚函数，如果不覆盖，那么 `Derived` 会直接使用 `Base` 的版本。

- 在覆盖的函数前使用 `virtual` 修饰（非必须，因为虚函数继承后还是虚函数）
- 可以用 `override` 显式指出被覆盖的函数，写在形参列表后面。(`const` 之后，引用限定符之前），防止将非虚函数改写或者未改写函数而是定义了新函数

### `Derived` 向 `Base` 的类型转换

`Derived` 对象可以被看作多部分：`Derived` 自己定义的非 `static` 成员，以及从各个 `Base` 继承而来的成员。因为 `Derived` 含有和 `Base` 相同的组成部分，所以可以把 `Derived` 当作 `Base` 使用，并绑定到 `Base` 的引用或指针。

即 `Derived` 到 `Base` 的转换。

``` cpp
Quote item;
Bulk_quote bulk;
Quote *p = &bulk;
Quote &r = bulk;
```

### `Derived` 构造函数

`Derived` 的 `Base` 部分必须通过 `Base` 的构造函数来初始化。（不能自己初始化）

``` cpp
Bulk_quote(const std::string &book, double p, std::size_t qty, double disc):
    Quote(book, p), min_qty(qty), discount(disc) {} // Base 的成员必须通过 Base 的构造函数初始化
```

应该先初始化 `Base` 部分的成员，再初始化剩下的 `Derived` 部分。

### `Derived` 使用 `Base` 的 `static` 成员

`Base` 定义的 `static` 成员是唯一的，由 `Derived` 和 `Base` 共享（不会因为有 `Derived` 就重复定义）。

### `Derived` 的声明与定义

`Derived` 类的声明不能包含类派生列表。

``` cpp
class Derived: public Base {} // 非法
class Derived; // 合法
```

`Base` 的定义（非声明）必须在 `Derived` 之前，因为 `Derived` 中的成员要访问 `Base` 中的成员。因此一个类不能继承自己。

``` cpp
class Base;
class Derived: public Base {} // 错误，必须是定义在 Derived 之前
```

`Derived` 又可以作为另一个类的 `Base`，这个类会继承祖先所有的成员。（**间接继承**）

``` cpp
class Base {}
class Derived1: public Base {} // 可以访问 Base 的成员
class Derived2: public Derived1 {} // 可以访问 Base + Derived 的成员
```

### 用 `final` 防止继承

用 `final` 关键字可以防止一个类被继承。

``` cpp
class NoDerived final {}
class Bad: public NoDerived {} // 非法
```

## 继承与类型转换

可以把 `Base` 的指针和引用绑定在 `Derived` 上，使用 `Base` 的指针和引用时，实际上可能在使用 `Derived` 的对象。

### 静态类型和动态类型

表达式的**静态类型**在编译期已知，**动态类型**在运行时可知。非引用和指针的变量，其静态类型与动态类型相同，但是 `Base` 的指针或引用的动态类型可能与静态类型不相同。

- `Derived` 可以向 `Base` 转换，因为 `Derived` 包含了 `Base` 的一部分。但是转换只对**指针**和**引用**有效。如果是直接值拷贝对象或者用 `Derived` 初始化 `Base`，那么 `Derived` 多余的部分会被切掉。（变成了真正的 `Base`）
- 反过来，`Base`不能转换为 `Derived`。即使一个 `Base` 指针或引用绑定了一个 `Derived` 对象，但是依然不可以将它转换为 `Derived`。（因为编译器无法检查出这种关系）除非用 `dynamic_cast`（运行期检查）或 `static_cast`（强制转换）。

``` cpp
Derived d;
Base &rb = d;
Base b = d;
// print 在 Derived 中被 override
rb.print(); // Derived 的 print 函数
b.print();  // Base 的 print 函数
```

# 虚函数

如果函数是虚函数，那么它被继承后仍然是虚函数。虚函数通过指针或引用调用时会发生动态绑定。（只有在指针和引用中会发生动态绑定）

`Derived` 如果覆盖 `Base` 的虚函数，那二者的**形参类型**和**返回值**、**`const` 修饰**等修饰属性必须完全相同。唯一的例外是如果函数返回类本身的指针或引用，那么只要求 `Derived` 能转换成 `Base`。（即返回值为 `Base*` 的虚函数可以被覆盖为返回值为 `Derived*` 的虚函数）

## `override` & `final`

如果定义了一个与 `Base` 中虚函数形参或返回类型不同的同名函数，那么编译器会认为这两个函数是独立的函数。
所以为了避免覆盖虚函数时写错形参列表（导致编译器认为两个函数独立），可以用 `override` 显式声明这个函数将覆盖原虚函数，编译器会检查是否真的覆盖了某个虚函数。

将一个虚函数声明为 `final` 可以防止被覆盖。（非虚函数不可以）

``` cpp
struct B {
    virtual void f1(int) const;
    virtual void f2();
    void f3();
    virtual f4() final;
};

struct D: B {
    void f1(int) const override; // 合法

    void f1(int) override; // 非法，const 不同
    void f2(int) override; // 非法，形参不同
    void f3() override; // 非法，原函数没有 virtual

    void f4(); // 非法，原函数为 final
};
```

## 虚函数的默认实参

虚函数调用时的默认实参与静态类型（即 `Base`）的函数定义为准。（因为实参绑定在编译期）即使对象是 `Derived`，通过 `Base` 的指针和引用调用的仍然是 `Base` 的默认实参，但是函数是 `Derived` 的函数。

因此，最好让 `Base` 和 `Derived` 虚函数的默认实参相同相同。

## 回避虚函数的动态绑定

用 `::` 可以强制执行某个虚函数版本（此时在编译期完成解析）。通常用在只需要处理 `Base` 部分的数据，而不想要处理 `Derived` 部分数据时使用。

``` cpp
double base_data = baseP -> Base::get_data(); // 强制使用 Base 的 get_data() 函数
```

# 抽象基类

## 纯虚函数

虚函数要求函数必须被定义，而**纯虚函数**允许在 `Base` 中不被定义，用 `=0` 进行标记（只能在声明处标记）。

``` cpp
class Disc_quote {
public:
    virtual double net_price(std::size_t) const = 0; // 纯虚函数
};
```

可以在类的外部为纯虚函数提供定义（必须和声明在同一个文件中，并且仍然不能定义对象），但只能在子类中通过 `Disc_quote::net_price` 使用，相当于提供了**默认实现**。

虽然纯虚函数此时没有定义，但是类中其它成员函数可以调用它。（纯虚函数只是暂时不提供实现，虚函数表中仍有位置）

## 抽象基类

含有纯虚函数的类被称为**抽象基类**。

抽象基类只负责定义接口，可以定义构造函数等。但是抽象基类不能定义对象，它的 `Derived` 必须覆盖这些接口才能定义对象。

抽象基类的 `Derived` 一般会通过抽象基类本身的构造函数来初始化抽象基类的部分。

## `Derived` 只能初始化直接 `Base`

如继承关系 `Base → aBase → Derived`。

- `Base` 初始化自己
- `aBase` 调用 `Base` 的构造函数初始化它，并且初始化自己
- `Derived` 调用 `aBase` 的构造函数初始化它，并且初始化自己（不应该直接调用 `Base` 的部分）

# 访问控制与继承

- `public`：都可以访问
- `protected`：`Derived` 和 `Derived` 的友元可以访问 `Derived` 的 `protected` 成员（不能访问 `Base` 的），用户无法访问
- `private`：仅成员和友元可以访问

> 类派生列表控制访问时，用户只能访问 `public`, `Derived` 只能访问 `public` 和 `protected`。
>
> `Base` 三者皆可。

**是否可访问由静态类型决定，访问哪个版本由动态类型决定。**

## 类派生列表的访问控制

`Derived` 访问 `Base` 对象成员受两个因素控制

- `Base` 中的访问控制：限定了 `Derived` 和用户对成员的访问
- `Derived` 的派生列表中的访问控制：限制了**用户**和**继承类**对于 `Base` 中成员的访问

如果使用了 `private` 继承，那么对于 `Derived` 无影响，但是 `Derived` 的用户和继承类则所有成员变成了 `private`。

``` cpp
class Base {
public:
    void pub_mem();
protected:
    int prot_mem;
    char priv_mem;
};

struct Pub_Derv: public Base {
    int f() { return prot_mem; } // 合法
    char g() { return priv_mem; } // 非法
};

struct Priv_Derv: private Base {
    int f() { return prot_mem; } // 合法
    char g() { return priv_mem; } // 非法
};

Pub_Derv d1;
Priv_Derv d2;
d1.pub_mem(); // 合法
d2.pub_mem(); // 非法

struct Derived_from_Public : public Pub_Derv {
    int use_base() { return prot_mem; } // 合法
};

struct Derived_from_Public : public Priv_Derv {
    int use_base() { return prot_mem; } // 非法
};
```

## `Derived` 向 `Base` 转换的可访问性

类派生列表对转换的影响：

- 用户 : 只有当继承方式为 `public` 时，用户才能把 `D` 类型转换成 `B` 类型，否则不行
- `D` : `D` 的成员函数和友元总是能将 `D` 转换为 `B`
- `D` 的 `Derived` : 只有当继承方式为 `public` 或 `protected` 时，`D` 的 `Derived` 才能将 `D` 转换为 `B`

## 友元与继承

友元关系不能继承。

`Base` 的友元不能访问 `Derived`, `Derived` 的友元也不能访问 `Base`。（但是能访问 `Derived` 中的 `Base` 部分）

``` cpp
class Base {
    friend class Pal;
protected:
    int prot_mem;
};

class Sneaky : public Base {
    int j;
};

class Pal {
    int f(Base b) { return v.prot_mem; } // 合法
    int f2(Sneaky s) { return s.j; } // 非法
    int f3(Sneaky s) { return s.prot_mem; } // 合法，实际上是访问 Base
}
```

## 用 `using` 改变可访问性

`using` 语句的可访问性取决于其所在的访问控制符。

``` cpp
class Base {
public:
    int i;
private:
    int j;
};

class D: private Base { // private 继承，i, j 都相当于 D 的 private 对象，用户和派生类不可访问
public:
    using Base::i; // 将 Base::i 变为 D 的 public 对象，用户和派生类可访问
protected:
    using Base::j; // 将 Base::j 变为 D 的 protected 对象，派生类可访问
};
```

## 默认继承方式

`Derived` 如果用 `class` 默认以 `private` 继承，如果用 `struct` 默认以 `public` 继承。

# 类作用域

存在继承关系时，`Derived` 的作用域嵌套在 `Base` 的作用域内。名字的搜索从当前类型的作用域开始。

定义在内层的名字可以隐藏定义在外层的名字，如果要访问外层名字可以用作用域符号。

``` cpp
class Derived: public Base {
public:
    int get_base_num { return Base::num; }
private:
    int num;
};
```

## 继承中的名字查找过程

静态类型决定对象能访问哪些成员，动态类型决定对象访问的是哪一个版本。

``` cpp
// 继承关系：B → D1 → D2
// D1 定义了函数 public foo
D2 d;
B *b = d;
d.foo(); // 合法
b->foo(); // 非法
```

- 确定静态类型（指针或引用的显式类型），在静态类型的作用域开始，从内到外找名字
- 一旦找到了，判断类型是否匹配，不匹配非法
- 若匹配，检查函数是否是虚函数，如果是虚函数且通过指针和引用调用，则使用动态绑定；否则使用静态绑定

## 名字查找优先于类型查找

内层名字会隐藏外层名字，并且名字查找优先于类型查找。如果内外重名，则只看内层。

``` cpp
struct Base{
    void foo();
};

struct Derived: public Base {
    void foo(int);
};

Derived d;
d.foo(1); // 合法
d.foo(); // 非法，外层名字被内层掩盖
```

## 覆盖重载的函数

首先无论是不是虚函数都可以被覆盖（只是是否发生动态绑定的区别）。

**“名字查找优先于类型查找”**的规则导致，如果 `D` 重载了 `B` 的某个函数，那么 `D` 要把所有同名函数都覆盖一遍，否则一些 `B` 的同名函数会被隐藏。

此时可以用 `using` 解决问题。使用 `using` 可以把外部的名字暴露进来，不需要指定形参列表。重载的函数只要跟在 `using` 之后就好了。对于重载的版本会直接访问重载版本，对于不重载的版本会访问 `Base::f` 的版本。

``` cpp
using Base::f;
// 重载 f 函数
```

# 构造函数与拷贝控制

## 虚析构函数

有继承关系的类的析构函数必须是虚析构函数。发生动态绑定时，`Base` 的指针指向的可能是 `Derived` 的对象，如果不使用虚析构函数，此时销毁 `Derived` 会调用 `Base` 的析构函数，因此只会释放 `Base` 的资源，即发生了内存泄露。

``` cpp
class Base {
public:
    virtual ~Base() = default;
};
```

在 `Base` 中三五法则失效（有可能定义析构函数只是为了让它成为虚析构函数，注意会阻止合成移动操作）。

## 合成的拷贝控制与继承

`Derived` 的合成的拷贝控制会自动运行 `Base` 对应的拷贝控制操作。

- 对于构造函数，先执行 `Base` 的构造函数，再执行 `Derived` 的构造函数
- 对于析构函数，先执行 `Derived` 的析构函数，再执行 `Base` 的析构函数

要使用成员的拷贝控制，就要求成员可访问，并且不是一个被删除的函数。

- 如果 `Base` 的**默认构造函数**、**拷贝函数**、**析构函数**被定义为删除或不可访问，则 `Derived` 的对应函数也会被定义成删除的（基类部分的操作需要这些函数）
- `Base` 的**析构函数**是删除或不可访问的，则 `Derived` 的**合成的默认和拷贝构造函数**也被定义为删除的
- 如果 `Base` 的**移动操作**或**析构函数**被删除或无法访问，则 `Derived` 的**移动操作**被删除

### `Derived` 的拷贝和移动成员

`Derived` 的**构造函数**、**拷贝函数**、**移动函数**要处理 `Base`（直接基类）的成员
（通过委托的方式进行），而**析构函数**只要处理自己的成员。

``` cpp
class Base {};

class Derived {
public:
    D(const D& d) : Base(d) {
        // 处理 Derived 部分
    }
    D(D&& d) : Base(std::move(d)) {
        // 处理 Derived 部分
    }
};
```

### `Derived` 的赋值运算符

与拷贝和移动构造函数一样，`Derived` 的赋值运算符也必须显式地为其 `Base`（直接基类）部分赋值。

``` cpp
D& D::operator=(const D &rhs) {
    Base::operator=(rhs); // 为 Base 部分赋值
    // 处理 Derived 部分
    return *this;
}

D& D::operator=(const D &&rhs) {
    // 处理 Derived 部分
    Base::operator=(std::move(rhs)); // 为 Base 部分赋值
    return *this;
}
```

### `Derived` 的析构函数

对象的 `Base` 部分会进行隐式销毁，因此 `Derived` 的析构函数只要销毁自己的成员。

``` cpp
class Derived : public Base {
    ~D() {
        // 处理 Derived 的成员
        // 自动调用 Base::~Base()
    }
};
```

### 在构造函数和析构函数中调用虚函数

在 `Base` 的构造函数或析构函数中调用虚函数时，会直接调用 `Base` 版本的虚函数。

因为在构造函数执行时，`Derived` 的成员未构建；析构函数执行时，`Derived` 的成员已销毁，此时无法调用 `Derived` 版本的虚函数，编译器会自动调用 `Base` 版本。

## 继承构造函数

用 `using` 可以继承构造函数，`using Base::Base` 会被展开为一系列的 `Derived (parms) : Base(args) {}`。

``` cpp
class Base {
  Base(int i) {}
  Base(double d,int i) {}
  Base(float f,int i,const char* c) {}
  // ...
};

class Derived: public Base {
  using Base::Base; // 等价于三个构造函数
  //......
};
```

其中 `Derived` 自己成员会被默认初始化。

### 用于构造函数的 `using` 特性

构造函数的 `using` 不会改变访问级别（`public`, `private`, `protected`），也不会改变 `explicit` 与 `constexpr` 属性。

对于有默认实参的构造函数，则含有默认实参的构造函数会被拆分为多个版本，每个版本分别省略一个参数。如函数 `Base(int, double=1.5)` 会被拆成 `Base(int)` 与 `Base(int, double)`。

`using` 构造函数会继承所有构造函数，但是存在两个例外：
- 如果 `Derived` 定义的构造函数与 `Base` 的构造函数有相同的参数列表，则该构造函数将不会被继承（即使用 `Derived` 的版本）
- **默认**、**拷贝**、**移动**构造函数不会被继承，这些构造函数按照正常规则被合成

# 容器与继承

要在容器中存放具有继承关系的对象，必须用（智能）指针，而不能直接存放对象。

派生类的智能指针也可以转换为基类的智能指针。

``` cpp
std::vector<std::shared_ptr<Quote>> basket;

basket.push_back(std::make_shared<Quote>("0-2-1-82470-1", 50));
basket.push_back(std::make_shared<Bulk_quote>("0-201-54848-8", 50, 10, 0.25));
std::cout << basket.back()->net_price(15) << std::endl;
```

通常会把带容器的继承对象再封装成一个类。

## 模拟虚拷贝

对一个引用或指针进行拷贝操作时，会遇到动态类型的问题：如果使用 `new Base()` 分配内存，会导致放不下 `Derived` 的额外空间。

因此需要每个类自己定义虚拷贝操作。

``` cpp
class Base {
public:
    virtual Base* clone() const & {
        return new Base(*this);
    }
    virtual Base* clone() const && {
        return new Base(std::move(*this));
    }
};

class Derived : public Base {
public:
    Derived* clone() const & {
        return new Derived(*this);
    }
    Derived* clone() const && {
        return new Derived(std::move(*this));
    }
};

class Basket {
public:
    void add_item(const Base& sale) {
        items.insert(std::make_shared(std::shared_ptr<Base>(sale.clone())));
    }
    void add_item(const Base&& sale) {
        items.insert(std::make_shared(std::shared_ptr<Base>(std::move(sale).clone())));
    }
}
```
