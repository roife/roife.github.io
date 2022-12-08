---
layout: "post"
title: "「C++ Primer」 13 Copy Control"
subtitle: "拷贝控制"
author: "roife"
date: 2020-08-01

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 拷贝控制

拷贝控制操作分为五种：

- 拷贝构造函数，移动构造函数：对象初始化
- 拷贝赋值函数，移动赋值函数：对象赋值
- 析构函数：对象销毁

编译器会默认为缺失的操作定义默认控制函数，但是默认定义不一定正确。

# 拷贝，赋值，析构

## 拷贝构造函数

如果一个构造函数的第一个参数是对自身的引用，且其余的参数都有默认值，那这是一个**拷贝构造函数**。

``` cpp
class A {
public:
    A(); // 默认构造函数
    A(const A &); // 拷贝构造函数
};
```

- 拷贝构造函数的第一个参数必须是引用类型（否则拷贝调用将无限进行，因为值传递的过程中就需要用到拷贝构造函数）
- 一般是 `const` 引用
- 拷贝构造不应该定义成 `explicit`

### 合成拷贝构造函数

即使定义了其它构造函数，编译器也会合成一个拷贝构造函数。

除了一些特殊情况，合成拷贝构造函数会将每个非 `static` 成员逐个拷贝到另一个对象上。

- 对于类类型，会利用它的拷贝构造函数
- 对于内置类型，会直接拷贝
- 对于数组，会逐个拷贝每个成员

### 拷贝初始化

拷贝初始化通常使用拷贝构造函数（有时也使用移动构造函数）。

拷贝初始化除了在变量定义的过程中发生，还在以下的情况中进行

- 非引用形参的传递和函数返回值
- 花括号初始化数组元素或聚合类
- 标准库容器的 `insert()` 或 `push_back()` 操作等（`emplace()` 会直接初始化）

``` cpp
std::string s2(s); // 直接初始化
std::string s3 = s2; // 拷贝初始化
std::string s4 = ".........."; // 拷贝初始化，必要时进行类型转换
std::string s5 = std::string(10, '.'); // 拷贝初始化

void f(std::vector<int>);
f(std::vector<int>(10)); // 拷贝初始化
```

拷贝初始化时，编译器可以选择略过拷贝复制函数进行直接初始化。（优化）

``` cpp
std::string s = std::string("str");
// 可能被优化为
std::string s2("str");
```

## 拷贝赋值运算符

赋值运算符会结合析构函数和构造函数的功能，即将左侧的对象析构，然后构造。

赋值运算符一定要考虑自赋值的情况。

``` cpp
class A {
public:
    A& operator=(const A&); // 赋值运算符，一般返回左侧对象的引用
};

A& A::operator=(const A&) {
    // ...
    return *this; // 不能遗漏！
}
```

### 合成拷贝赋值运算符

如果类没有定义拷贝赋值运算符，编译器会进行自动合成。

默认情况下，合成拷贝运算符会将右侧运算对象的非 `static` 元素逐个拷贝到左侧。（类似于默认拷贝构造函数）

## 析构函数

析构函数释放对象占用的资源，并销毁对象的非 `static` 成员。

析构函数不接受参数，也不能被重载，因此它是唯一的。

``` cpp
class A {
public:
    ~A(); // 析构函数
};
```

在析构函数中，先执行函数体，再按照初始化的顺序销毁对象，类类型的对象会调用各自的析构函数。（和构造函数相反）

析构函数的函数体并不会直接销毁成员。（和拷贝函数相反）

### 析构函数被调用的时刻

- 变量离开作用域
- 对象被销毁时，它的类对象成员会调用析构函数
- 容器被销毁，元素被销毁时
- 动态分配的对象被 `delete`
- 对于临时的对象，当整个表达式结束时被销毁

对于引用或者一个指针指向的对象，离开作用域后不会被销毁。

### 合成析构函数

编译器可以合成析构函数，只执行默认的销毁操作。

## `=default`

- `=default`：显式要求使用合成函数

类内声明 `=default` 时函数会 `inline`，类外不会。

``` cpp
class Sales_data {
public:
    Sales_data() = default; // inline
    Sales_data(const Sales_data&) = default;
    Sales_data& operator=(const Sales_data&);
    ~Sales_data() = default;
};

Sales_data& Sales_data::operator=(const Sales_data&) = default; // 不 inline
```

## `=delete`

有时候会要求阻止拷贝。（比如 `std::iostream` 为了避免多个对象同时操作一个流）

`=delete` 必须在函数第一次声明时指出。（方便编译器检查错误）

``` cpp
class A {
    A() = default;
    A(const A &rhs) = delete; // 阻止拷贝
    ~A() = default;
};
```

### 删除析构函数

删除析构函数会导致类无法销毁对象，因此编译器不允许创建这个类的变量或临时对象，包含这种类型成员的类也不能创建对象或临时对象（但是类中可以声明）。

可以为删除析构函数的类创建动态对象，但是无法释放内存。

``` cpp
class A {
    A() = default;
    ~A() = delete;
};

A a; // 非法
A *p = new A(); // 合法，但是不能 delete p
```

### 用 `=delete` 控制函数匹配

`=delete` 不止可以用于构造函数，也可以用于普通函数来引导匹配。

``` cpp
class A {
    A() = default;
    A(int i) {}
    A(char c) = delete;
};
```

当没有 `A(char c) = delete` 时，`A('a')` 会被匹配到 `int` 的函数。定义了之后就不会发生隐式类型转换。

### 默认删除的合成拷贝控制成员

- 成员的**默认构造/拷贝/析构函数**被删除或无法访问，那么这个类**对应的合成函数**也被删除（无法合成）

- 成员的**析构函数**被删除，那么这个类的**合成默认构造函数**、**合成拷贝构造函数**被删除（否则对象可能无法删除）

- 引用成员、`const` 成员**未初始化**，那么这个类的**合成默认构造函数**被删除（引用或 `const` 成员要求初始值）

- **存在**引用成员或`const` 成员，那么这个类的**合成拷贝赋值运算符**被删除（无法赋值）

### 用 `private` 控制拷贝

在新标准之前，通常将拷贝控制函数声明为 `private` 来阻止拷贝。同时为了防止 `friend` 与成员函数访问，可以只声明不定义。（若试图访问会发生链接错误）

``` cpp
class PrivateCopy {
    PrivateCopy(const PrivateCopy&); // 默认为 private，阻止拷贝
    PrivateCopy& operator=(const PrivateCopy&);
};
```

# 交换操作

对于管理资源的类，交换操作也是重要的一部分。标准库中的 `std::swap()` 函数通过普通的赋值进行交换会发生资源拷贝，因此需要自己定义 `swap()` 过程。

``` cpp
A temp = v1; // 这一步使用了拷贝赋值运算符，发生了资源的拷贝，开销可能很大
v1 = v2;
v2 = temp;
```

交换资源应使用移动的方式而非拷贝。

``` cpp
class A {
    friend void swap(A&, A&);
// ...
private:
    std::string *ps;
    int i;
};

inline void swap(HasPtr &lhs, HasPtr &rhs) {
    using std::swap;
    swap(lhs.ps, rhs.ps); // 只交换指针
    swap(lhs.i, rhs.i);
}
```

使用 `swap()` 时，自定义的 `swap()` 由于类型特定会优先匹配，因此即使有 `using std::swap;`，也不用担心会调用 `std::swap()`。

## `swap()` 与拷贝赋值运算符

定义了 `swap()` 函数后可以在拷贝赋值运算符中简化代码，自动处理了自赋值的问题：交换右侧对象的副本与当前对象。

``` cpp
HasPtr& HasPtr::operator=(const HasPtr rhs) { // 注意这里的 rhs 不是引用，隐含了拷贝构造函数
    swap(*this, rhs);
    return *this;
} // 隐含了析构函数的调用
```

# 对象移动

一些情况下，用移动来代替拷贝可以减少花销，而且可以满足特殊类型的要求（如 IO 类和 `std::unique_ptr`），可以简单理解为指针操作，值类型不能进行移动。

## 右值引用

右值引用绑定在右值上，但是不能绑定在左值上，因为右值引用要求被绑定的原对象不再使用（因为所有权转移了，可以自由接管资源），相当于"窃取"资源。

``` cpp
int i = 42;

int &r = i; // 正确
int &r2 = i * 42; // 错误
const &r3 = i * 42; // 正确

int &&rr = i; // 错误，右值引用不能绑定在左值上
int &&rr2 = i * 42; // 正确，实际上是右值所有权的转移
```

右值只能被绑定在临时对象上，生命期是短暂的。（左值生命期是持久的）

- 所引用的对象将被销毁
- 该对象没有其他用户

### `std::move`

`std::move` 定义在 `utility` 头文件中，可以将左值显式转换为右值。

``` cpp
int &&rr3 = std::move(rr1); // 转换之后要求不能再使用 rr1 中的对象！（只能给 rr1 赋予新值或者销毁 rr1）
```

一般直接使用 `std::move` 这个名字，而不使用 `using` 声明。（模板匹配时的问题）

## 移动构造函数和移动赋值运算符

移动控制函数用于移动资源而非拷贝资源，开销更低。移动构造函数的第一个参数必须是右值引用，且其他参数都有默认值。

除了移动资源，移动控制函数必须使原对象不再指向它的资源（即保证可以无害地析构和销毁）。对象移动后必须能够被析构，而且不能影响其资源。（通常把指针设置为 `nullptr`）

``` cpp
StrVec::StrVec(StrVec &&s) noexcept // 没有 const，且移动操作不应抛出异常
    elements(s.elements), first_free(s.first_free), cap(s.cap) { // 移动元素
    s.elements = s.first_free = s.cap = nullptr; // 保证 s 原来的资源不能再通过 s 访问，可以正常析构
}
```

### 移动，标准库与异常

移动操作不会分配资源，也不会抛出异常，所以可以用 `noexcept` 来声明不抛出异常。

异常机制要求容器在发生异常时能够回退状态，但是移动操作进行到一半时若发生异常，由于原始对象数据已被部分清除，难以进行数据恢复，所以标准库会使用拷贝构造函数。使用了 `noexcept` 之后，可以避免标准库使用拷贝的开销。

使用 `noexcept` 时写在初始化器的冒号前面。

``` cpp
StrVec::StrVec(StrVec &&s) noexcept {}
```

### 移动赋值运算符

和移动构造函数一样，移动赋值运算符也应该声明为 `noexcept`，且要能处理自赋值。

``` cpp
StrVec&
StrVec::operator=(const StrVec&& rhs) noexcept {
    if(this != &rhs) { // 判断自移动
        free(); // 释放左侧资源
        elements = rhs.elements; // 直接赋值指针，而不拷贝资源
        first_free = rhs.first_free;
        cap = rhs.caps;
        rhs.elements = rhs.first_free = rhs.caps = nullptr; // 保证右侧可以正常析构
    }
    return *this;
}
```

### 合成移动操作

- 如果自己定义了**拷贝构造函数**/**拷贝赋值运算符**/**析构函数**，那么编译器就不会合成**移动构造函数**和**移动赋值运算符**（此时全部使用拷贝操作）
- **成员**的移动操作被定义为删除或无法访问，则类的移动操作也被定义为删除
- 类的**析构函数**被定义为删除或无法访问，则类的移动函数被定义为删除
- 类成员存在**引用**或 **const成员**，则类的移动操作被定义为删除
- 对于定义了**移动操作**的类，编译器不会自动**合成拷贝函数**

只有当一个类没有定义这三个函数，而且类的每个非 `static` 成员都可以被移动时（是内置类型或有移动操作的类类型）,
编译器才会合成移动构造函数和移动赋值运算符。

### 移动函数的匹配

编译器会根据函数的返回值来选择使用拷贝复制还是移动赋值。

左值拷贝，右值移动。

``` cpp
StrVec v1, v2;
v1 = v2; // 拷贝赋值
StrVec getVec(istream&); // 返回右值
v2 = getVec(cin); // 移动赋值
```

但是如果只有拷贝构造函数，没有移动构造函数，那么会始终使用拷贝操作（因为编译器也不会合成移动操作）。

### 利用交换操作实现移动

赋值时如果既有移动构造函数，又有拷贝构造函数，具体移动还是拷贝看调用处是右值还是左值。

```cpp
class HasPtr {
public:
    HasPtr (HasPtr &&p) noexcept : ps(p.ps), i(p.i) { p.ps = 0; }
    HasPtr& operator= (HasPtr rhs) { swap(*this, rhs); return *this; } // swap() 之后 rhs 指向 *this，正好被销毁
}
hp = hp2; // 拷贝构造
hp = std::move(hp2); // 移动构造
```

## 移动迭代器

移动迭代器的解引用返回一个右值。

可以用 `std::make_move_iterator()` 将普通迭代器转换为移动迭代器。

``` cpp
auto last = std::uninitialized_copy(
    std::make_move_iterator(begin()),
    std::make_move_iterator(end()),
    first);
```

并非所有算法都能用移动操作，使用前必须要确保该函数可以使用移动迭代器。

## 三/五法则

一个类如果定义了五个拷贝操作中的任意一个，就应该定义剩下的操作。

## 成员函数与右值

通常成员函数可以定义两个版本：`const` 左值引用和非 `const` 右值引用（因为窃取数据后要清空原对象）。

``` cpp
void push_back(const X&); // 拷贝
void push_back(X&&); // 移动（精确匹配）
```

### 引用限定符

在参数列表后用 `&` 和 `&&` 可以限定 `this` 是左值还是右值（即当前函数的对象是左值还是右值）。

引用限定符只能用在非 `static` 函数中，必须在声明和定义中同时出现，且必须出现在 `const` 后面。

``` cpp
class Foo {
public:
    Foo &operator= (const Foo&) &;
    Foo someMem() const &; // 正确
};

Foo &Foo::operator=(const Foo &rhs) & {
    return *this;
}
```

右值限定的成员函数可以直接在对象进行操作，而左值成员函数必须拷贝一个新对象。（提高效率）

``` cpp
class Foo {
public:
    Foo sorted() &&;
    Foo sorted() const &;
private:
    std::vector<int> data;
};

Foo Foo::sorted() && {
    std::sort(data.begin(), data.end());
    return *this;
}

Foo Foo:sorted() const & {
    Foo ret(*this); // 左值必须要拷贝一份
    std::sort(ret.data.begin(), ret.data.end());
    return ret;
}
```

引用限定符也可以重载。如果用了引用限定符，那么所有同名函数必须都加上，或者都不加。
