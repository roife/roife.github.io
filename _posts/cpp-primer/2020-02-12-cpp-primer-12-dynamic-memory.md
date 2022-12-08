---
layout: "post"
title: "「C++ Primer」 12 Dynamic Memory"
subtitle: "动态内存管理与智能指针"
author: "roife"
date: 2020-02-12

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 静态内存与动态内存

- 静态内存：全局变量，局部 `static` 变量，类的 `static` 成员
- 栈内存：函数的非 `static` 变量
- 堆：动态分配的变量

静态内存与栈内存由编译器进行创建和销毁，堆对象的生命周期要手动控制和显式销毁。

# 直接管理内存（`new`、`delete`)

- `new`：在动态内存中为对象分配空间，返回指向该对象的指针
- `delete`：传递一个动态对象的指针，销毁对象并释放关联的内存

## 分配内存

- 直接分配内存：默认初始化（内置类型的值不确定，类类型使用默认构造函数）
- 在语句后面加一对括号：值初始化
- 花括号：列表初始化

``` cpp
int *pi = new int; // 默认初始化，值不确定
std::string *ps = new std::string; // 默认初始化，空字符串

int *pi2 = new int(1024); // 1024
int *p3 = new int(); // 0

std::vector<int> *pv = new std::vector<int> {0, 1, 2, 3, 4, 5};
```

可以用 `auto` 和一个初始化值（必须是单一的一个）来推断类型。

``` cpp
auto p1 = new auto(obj); // *p1 = obj;
auto p2 = new auto{a, b, c}; // 非法
```

## 分配 `const` 对象

`const` 对象必须直接初始化（类类型可以用构造函数隐式初始化），返回一个 const 指针。

``` cpp
const int *pci = new const int (1024);
const std::string *pcs = new const std::string;
```

## 异常

当内存耗尽时空间分配失败，抛出 `std::bad_alloc` 异常，定义在头文件 `new` 中。用 placement new 和 `std::nothrow` 对象可以阻止它抛出异常（使其返回 `nullptr`）。

``` cpp
int *p2 = new (std::nothrow) int;
```

## `delete`

可以用 `delete` 释放 `new` 的对象（或者 `nullptr`）。

## dangling pointer

被 `delete` 之后的指针成为了一个无效的 dangling pointer。及时将无效指针设置为 `nullptr`，可以一定程度上规避 dangling pointer。

但是当多个指针指向同一个对象时，仍可能出现问题：

``` cpp
int *p(new int (42)), *q = p; // p, q 指向同一个对象
delete p; // 空间被释放，p, q 都成为 dangling pointer
p = nullptr; // q 仍然是 dangling pointer
```

## 常见错误

1. 忘记 `delete`
2. 使用释放的对象（过早释放）
3. 同一块内存释放两次（UB）

# 智能指针

标准库提供了两种智能指针来管理动态对象，定义在 `memory` 头文件。

- `shared_ptr` 允许多个指针指向同一个对象
- `unique_ptr` 独占对象
- `weak_ptr` 指向 `std::share_ptr` 的对象

| 操作                           | 作用                                           |
| ------------------------------ | ---------------------------------------------- |
| `std::shared_ptr<T> sp`        | 空智能指针                                     |
| `std::unique_ptr<T> up`        | 同上                                           |
| `p`                            | 用于条件判断，返回是否指向对象                 |
| `*p`                           |                                                |
| `p->mem`                       |                                                |
| `p.get()`                      | 返回 `p` 保存的指针（注意对象被释放后指针失效）|
| `std::swap(p, q)`, `p.swap(q)` |                                                |

## `std::shared_ptr`

智能指针也是模板，需要指出对象的类型。

智能指针的使用方法和普通指针一样，如检测指针 `ps` 是否为空。

``` cpp
std::shared_ptr<std::string> ps; // 默认为 nullptr
if(ps && ps->empty()) *p1 = "hi";
```

| `std::shared_ptr` 独有操作   | 作用                                                                                              |
| ---------------------------- | ------------------------------------------------------------------------------------------------- |
| `std::make_shared<T> (args)` | 返回一个 `std::shared_ptr<T>`，并用 `args` 初始化                                                 |
| `std::shared_ptr<T> p(q)`    | 用 `std::shared_ptr<T2>` 的 `q` 初始化 `p`，要求类型能转化。此操作会递增 `q` 的引用计数           |
| `p = q`                      | `p` 和 `q` 都是 `std::shared_ptr`（类型能转换）。`p` 计数递减，`q` 计数递增。计数为 `0` 时对象释放 |
| `p.unique()`                 | 若 `p.use_count()==1` 则返回 `true`，否则为 `false`                                               |
| `p.use_count()`              | 与 `p` 共享对象的指针数量（涉及到多线程）                                                         |

### `std::make_shared`

注意，`std::make_shared<T>(args)` 中 `args` 不能直接用花括号列表，要用 `std::initializer_list({args})` 包装。

如果不传递参数，会进行值初始化。

``` cpp
std::shared_ptr<int> p3 = std::make_shared<int>(); // 没有参数则进行值初始化
std::shared_ptr<std::string> p4 = std::make_shared<std::string>(10, '9');
auto p6 = make_shared<std::vector<std::string>>();
```

### `std::shared_ptr` 的拷贝和赋值

`std::shared_ptr` 和一个引用计数关联：

- 被拷贝或者作为参数和返回值传递时，引用计数增加
- 指针被销毁或者被赋予新值时，引用计数减少
- 引用计数为 `0` 时，会调用析构函数释放对象

当 `std::shared_ptr` 被存放在容器中且不被使用时，可以及时释放来减少内存占用。

### 动态生存期

使用动态内存有三种原因

- 程序不知道要使用多少对象（`std::vector`）
- 程序不知道对象的准确类型（`void*`）
- 程序要在多个对象中共享数据（拷贝对象时通过引用实现）

## 智能指针与 `new`

可以用 `new` 返回的指针来初始化 `std::shared_ptr`。

由普通指针到智能指针的构造函数是 `explicit` 的，因此不能直接赋值（同样函数参数调用和返回时也要注意，不能进行隐式类型转换）。

``` cpp
std::shared_ptr<int> p1(new int (42));
std::shared_ptr<int> clone(int p) {
    return shared_ptr<int> (new int (42));
}

std::shared_ptr<int> p2 = new int (42); // 非法
std::shared_ptr<int> clone2(int p) {
    return new int(42); // 非法
}
```

用 `new` 来初始化 `std::shared_ptr` 开销很大！最好用 `std::make_shared`（`std::make_shared` 只会发生一次内存申请且线程安全，用 `new` 多了一次为 `std::shared_ptr` 申请空间的过程）

| 操作                            | 作用                                                                        |
| ------------------------------- | --------------------------------------------------------------------------- |
| `std::shared_ptr<T> p(q)`       | 用内置指针 `q` 初始化 `p`，要求类型可转换                                   |
| `std::shared_ptr<T> p(u)`       | 从 `p`（`std::unique_ptr`）中接管所有权，并将 `u` 置空                      |
| `std::shared_ptr<T> p(q, del)`  | 接管内置指针 `q` 指向对象的所有权，`p` 会调用 `del` 来释放对象              |
| `std::shared_ptr<T> p(p2, del)` | 接管 `p2`（`std::shared_ptr`）指向对象的所有权，`p` 会调用 `del` 来释放对象 |
| `p.reset()`                     | 若 `p` 是指向对象的唯一的 `std::shared_ptr`，则释放对象                     |
| `p.reset(q)`                    | 同上，释放后指向内置指针 `q`                                                |
| `p.reset(q, del)`               | 同上，调用 `del` 释放 `q`                                                   |

此处 `deleter` 的参数必须是 `(T *p)`。当指针指向一个类，且类中有动态内存的变量时，要自己定义 `deleter` 来释放这些内存。

### 混用普通指针和智能指针的风险

当智能指针接管普通指针时，不应该继续用普通指针访问内存，否则可能产生 dangling pointer（可以直接赋值 `nullptr`）。

``` cpp
auto pi = new int (42);
std::shared_ptr<int> sp1(pi);

{
    std::shared_ptr<int> sp2(pi); // 不应该继续用普通指针初始化了
} // 离开作用域，sp2 引用变为 0，释放空间
std::cout << *sp1; // 非法，dangling pointer
```

比如当做函数参数传递：

``` cpp
void process(std::shared_ptr<int> ptr) {} // 离开作用域时 ptr 被销毁。

std::shared_ptr<int> p(new int (42));
process(p); // 值形参传递时会发生拷贝，引用加一
int i = *p; // 调用完成 ptr 被销毁，引用减一，此时引用为 1，正确

int *x(new int (1024));
process(x); // 非法，智能指针构造函数为 explicit，无法发生隐式类型转换
process(std::shared_ptr(x)); // 合法，但是调用时引用计数为 1，销毁临时对象时引用计数为 0，此时内存会被释放！
int j = *x; // 非法，x 为 dangling pointer
```

### 慎用 `get()`

不要用 `get()` 函数返回的指针赋值给另一个智能指针。而 `get()` 函数返回的指针也不能被 `delete`。（当原来的智能指针被销毁时会发生二次销毁）

## RAII
发生异常时，手动管理的内存不会被回收，而局部智能指针对象销毁后会自动释放内存。一些没有定义析构函数的类或者资源，也可能出现资源未被释放的情况（如异常）。此时可以使用 `std::shared_ptr` 来管理对象。

通常情况下，`std::shared_ptr` 销毁对象时会调用 `delete` 操作。因此当其用于管理对象时，需要一个自定义的 `deleter`。

``` cpp
void f(destination&, ...) {
    connection c = connect(&d);
    std::shared_ptr<connection> pc(&c, end_connection);
    //...
    // 当函数结束或者发生异常时，pc 被销毁，自动调用 end_connection 结束链接
}
```

## 智能指针使用规范

- 不使用一个普通指针初始化（或 `reset`）多个智能指针
- 不 `delete` `get()` 得到的指针
- 不用 `get()` 初始化或者 `reset` 另一个智能指针
- 使用 `get()` 返回的指针在智能指针被销毁后会失效
- 使用智能指针管理资源时，要带一个 `deleter`
- 普通指针被赋予智能指针后要尽快设置为 `nullptr`

## `std::unique_ptr`

`std::unique_ptr` 不会共享对象，当 `std::unique_ptr` 被销毁，指向的对象也被销毁。

| `std::unique_ptr` 独有操作   | 作用                                                |
| ---------------------------- | --------------------------------------------------- |
| `std::unique_ptr<T> u1`      | 空指针，用 `delete` 释放                            |
| `std::unique_ptr<T, D> u2`   | 同上，用类型为 `D` 的可调用对象释放                 |
| `std::unique_ptr<T, D> u(d)` | 同上，调用类型为 `D` 的 `d` 释放                    |
| `u = nullptr`                | 释放对象，并把 `u` 变为 `nullptr`                   |
| `u.release()`                | 放弃对指针的所有权，返回指针，并令 `u` 为 `nullptr` |
| `u.reset()`                  | 释放对象                                            |
| `u.reset(q)`                 | 释放对象，并让 `u` 指向 `q`                         |
| `u.reset(nullptr)`           | 同上，将 `u` 置空                                   |

`std::unique_ptr` 没有类似与 `std::make_shared` 的函数，只能用内置指针进行直接初始化。

``` cpp
std::unique_ptr<int> p(new int (42));
```

### `release()` 与 `reset()`

`std::unique_ptr` 不支持拷贝与赋值（为了保证 `unique`），要通过 `release()` 和 `reset()` 转移所有权。

- `release()` 会切断所有权的联系，不会释放资源（因此 `release()` 时必须给另一个智能指针对象赋值）
- `reset()` 会释放资源

``` cpp
std::unique_ptr<int> p1(new int (42));
std::unique_ptr<int> p2(p1); // 非法
std::unique_ptr<int> p3 = p1; // 非法

std::unique_ptr<int> p4(p1.release()); // 合法，p1==nullptr
std::unique_ptr<int> p5;
p5.reset(p3.release()); // 合法，p3==nullptr
```

### `std::unique_ptr` 作参数或返回值

当 `std::unique_ptr` 将被销毁时，可以进行拷贝赋值（实际上是移动，例如函数返回一个 `std::unique_ptr`）。作为参数时应该使用 `std::move`。

``` cpp
std::unique_ptr<int> clone(int p) {
    return std::unique_ptr<int> (new int (p));
}

std::unique_ptr<int> clone(int p) { // 返回一个局部对象
    std::unique_ptr<int> ret(new int(p));
    // ...
    return ret;
}
```

早期 C++ 有一个 `std::auto_ptr`，类似与 `std::unique_ptr`，但是不能作为函数的返回值或者存储在容器中，因此已经被淘汰。

### `std::unique_ptr` 的 `deleter`

``` cpp
void f(descination &d, ...) {
    connection c = connect(&d);
    std::unique_ptr<connection, decltype(end_connection)*> p(&c, end_connection);
    // f 结束或发生异常时会调用 end_connction
}
```

## `std::weak_ptr`

`std::weak_ptr` 指向 `std::shared_ptr` 管理的对象，不控制所指对象的生命周期，不会改变引用计数，且不会影响对象的销毁过程。

| `std::weak_ptr` 独有操作 | 作用                                                                          |
| ------------------------ | ----------------------------------------------------------------------------- |
| `std::weak_ptr<T> w`     | 创建空 `std::weak_ptr`                                                        |
| `std::weak_ptr<T> w(sp)` | 用 `std::shared_ptr` 初始化 `std::weak_ptr`，要求类型能转化                   |
| `w = p`                  | `p` 是 `shared_ptr` 或 `weak_ptr`，赋值后共享对象                             |
| `w.reset()`              | 置空                                                                          |
| `w.use_count()`          | 与 `w` 共享对象的 `std::shared_ptr` 数量                                      |
| `w.expired()`            | 返回 `w.use_cound()` 是否为 `0`（对象是否被销毁）                             |
| `w.lock()`               | 若 `expired` 为假，返回对应的 `std::shared_ptr`，否则返回空 `std::shared_ptr` |

一个 `std::weak_ptr` 指向的对象可能已经被释放，需要用 `lock()` 来访问。

``` cpp
auto sp = std::make_shared<int>(42);
std::weak_ptr<int> wp(sp); // p 引用计数不变
// ...
if (std::shared_ptr<int> np = wp.lock()) { // 检验对象是否被释放
    // ...
}
```

# 动态数组

## `new` 数组

申请一片内存空间的语法是 `new *pointer = new T [Size]`（也可以使用数组别名）。

``` cpp
int *pia = new int [get_size()];

typedef int arrT[42];
int *p = new arrT;
```

### 遍历

定义动态数组时返回的是一个指向数组首元素的指针，因此不能用 `std::begin()` 和 `std::end()`，也不能用 range for，只能用普通的 `for` 循环。

``` cpp
std::size_t n = get_size();
int *p = new int [n];
for (int *q = p; q != p + n; ++q) {
    // ...
}
```

### 初始化

默认情况下分配的数组会被默认初始化，也可以用小括号来进行值初始化或者用花括号初始化。如果列表初始化的元素数量小于元素数目，剩余元素会被值初始化；反之会出现错误，抛出 `std::bad_array_new_length` 类型的异常（定义在头文件 `new` 中）。

不能用一个已有数组进行初始化，即不能使用 `auto p = new auto(obj)` 的语法。

``` cpp
int *pia1 = new int [10]; // 默认初始化
int *pia2 = new int [10](); // 值初始化
int *pia3 = new int [10]{0, 1, 2, 3, 4, 5, 6, 7, 8, 9};

std::string *psa = new std::string [10]; // 默认初始化，但是相当于值初始化
```

### 分配空数组

分配一个空数组也是一个合法的行为，但是这个指针不能解引用。

``` cpp
char arr[0]; // 非法

char *cp = new char[0]; // 合法，但是 cp 不能解引用
```

### 释放内存

释放动态数组的语法是 `delete [] arr`，提示编译器这是一个数组（即使是类型别名也要加上 `[]`）。

``` cpp
typedef int arrT[42];
int *p = new arrT;
delete [] p;
```

## 智能指针和动态数组

标准库允许用 `std::unique_ptr` 来管理动态数组：`std::unique_ptr<T[]> name(new T[Size]);`（一定要加放括号）。

``` cpp
std::unique_ptr<int[]> up(new int [10]);
up.release(); // 释放内存
```

此时不能使用 `.` 或者 `->`，但是可以用下标运算符。

## `std::allocate` 类

使用 new 分配数组时，所分配的对象会被立即初始化，可能会造成额外的开销，且没有默认构造函数的类无法进行动态分配数组。此时可以用 `std::allocator` 类，定义在 `memory` 头文件中。

`std::allocator` 类分配的内存是未构造的。它也是一个模板。

| 操作                   | 作用                                                                             |
| ---------------------- | -------------------------------------------------------------------------------- |
| `std::allocator<T> a`  |                                                                                  |
| `a.allocate(n)`        | 分配 `n` 个未构造的对象，返回首元素的指针                                        |
| `a.deallocate(p, n)`   | 释放指针 `p` 处开始的 `n` 个对象（和分配时对应）。调用前须 `destroy()` 创造的对象 |
| `a.construct(p, args)` | 在指针 `p` 处用 `args` 构造对象                                                  |
| `a.destroy(p)`         | 对指针 `p` 处的对象调用析构函数                                                  |

``` cpp
std::allocator<std::string> alloc;
auto const p = alloc.allocate(n); // 分配 n 个为初始化的对象
auto q = p;
alloc.construct(q++); // 生成一个空字符串
alloc.construct(q++, 10, 'c'); // 构造一个 10 个 c 的字符串

// 销毁对象
while (q != p) alloc.destroy(--q);
alloc.deallocate(p, n);
```

使用还未构造的空间将会发生错误。

头文件 `memory` 中还为 `std::allocator` 类定义了拷贝和填充未初始化内存的几个算法。

| allocator 算法                        | 作用                                                  | 返回                     |
| ------------------------------------- | ----------------------------------------------------- | ------------------------ |
| `std::uninitialized_copy(b, e, b2)`   | 将迭代器区间 `[b, e)` 拷贝到 `b2` 的原始内存处。| 尾元素后一个元素的迭代器 |
| `std::uninitialized_copy_n(b, n, b2)` | 从 `b` 开始，拷贝 `n` 个元素至 `b2` 处，即 `[b, b+n)` | 同上                     |
| `std::uninitialized_fill(b, e, t)`    | 将指向原始内存的迭代器区间 `[b, e)`，全部初始化为 `t` | 同上                     |
| `std::uninitialized_fill_n(b, n, t)`  | 从 `b` 处开始创建 `n` 个 `t`，即 `[b, b+n)`           | 同上                     |

这些算法都要保证目标处有足够的空间，且返回值都是处理的区域的尾后指针。

``` cpp
auto p = alloc.allocate(v.size() * 2);
auto q = std::uninitialized_copy(v.begin(), v.end(), p); // 将空间的前半部分用 vector 填充，{b, e} 是一对迭代器
std::uninitialized_fill(q, vi.size(), 42); // 将空间的后半部分用一个固定的数字填充
```
