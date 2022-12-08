---
layout: "post"
title: "「C++ Primer」 09 Sequential Containers"
subtitle: "顺序型容器"
author: "roife"
date: 2020-02-07

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 顺序容器概述

| 容器                | 作用           | 性能                             |
| ------------------- | -------------- | -------------------------------- |
| `std::vector`       | 变长数组       | 随机访问快，中间插入删除慢       |
| `std::deque`        | 双端队列       | 随机访问快，两端插入删除快       |
| `std::list`         | 双向链表       | 只能双向访问，任何位置插入删除快 |
| `std::forward_list` | 单向链表       | 只能单向查询，任何位置插入删除快 |
| `std::array`        | 大小固定的数组 | 支持随机访问，不能添加删除元素   |
| `std::string`       | 字符串         | 类似 `std::vector`               |

- 一般选择 `std::vector`
- `std::forward_list` 没有 `size()` 操作（为了性能）。对于其它容器，`size()` 是个常数时间。
- `std::list` 与 `std::forward_list` 额外的空间开销较大（因为要保存指针）。一般用于在中间插入删除数据频繁的地方。

# 容器库概览（对于所有容器库）

顺序容器可以接受任何类型，但是某些特殊类型不能使用部分操作（如 `std::vector` 接受数字进行初始化时，要求类类型能够默认初始化，否则需要提供一个初始化器，如 `std::vector<NoDefault>(10, init);`）

## 操作

### 类型

| 类型别名          | 作用                                            |
| ----------------- | ----------------------------------------------- |
| `iterator`        | 迭代器类型                                      |
| `const_iterator`  | `const` 迭代器类型                              |
| `size_type`       | 容器大小，类型为无符号整数                      |
| `difference_type` | 两个迭代器的距离，类型为带符号整数              |
| `value_type`      | 元素类型                                        |
| `reference`       | 元素的左值类型，即 `value_type&`                |
| `const_reference` | 元素的 `const` 引用类型，即 `const value_type&` |

类型的命名空间都在容器下，如 `std::container::iterator`。

### 初始化

| 构造函数       | 作用                                                       |
| -------------- | ---------------------------------------------------------- |
| `C c`          | 默认构造函数                                               |
| `C c1(c2)`     | 拷贝 `c2` 到 `c1`                                          |
| `C c(b, e)`    | 拷贝迭代器 `[b, e)` 之间的元素给 `c`（`std::array` 不支持）|
| `C c{a, b, c}` | 列表初始化                                                 |

顺序容器有一些特殊的构造函数。

| 顺序容器特有  | 作用                              |
| ------------- | --------------------------------- |
| `C seq(n)`    | `n` 个值初始化的元素（`explicit`） |
| `C seq(n, t)` | `n` 个初始值为 `t` 的元素         |

使用第一种时必须保证类类型支持默认初始化！

### 赋值与交换

| 赋值与交换       |
| ---------------- |
| `c1 = c2`        |
| `c1 = {a, b, c}` |
| `a.swap(b)`      |
| `swap(a, b)`     |

| `assign()` 操作    | 作用                                  |
| ------------------ | ------------------------------------- |
| `seq.assign(b, e)` | 将 `seq` 替换成迭代器 `[b, e)`        |
| `seq.assign(il)`   | 将 `seq` 替换成初始化列表             |
| `seq.assign(n, t)` | 将 `seq` 替换成 `n` 个值为 `t` 的元素 |

关联容器和 `std::array` 不能用 `assign()` 操作。

### 添加或删除元素

`std::array` 不适用。

| 添加/删除元素      | 作用                             |
| ------------------ | -------------------------------- |
| `c.insert(args)`   | 插入元素                         |
| `c.emplace(inits)` | 使用 `inits` 构造 `c` 的一个元素 |
| `c.erase(args)`    | 删除指定元素                     |
| `c.clear()`        | 删除 `c` 中所有元素              |

### 获取迭代器

| 迭代器                   | 作用                |
| ------------------------ | ------------------- |
| `c.begin()`, `c.end()`   | 返回迭代器          |
| `c.cbegin()`, `c.cend()` | 返回 `const` 迭代器 |

| 反向容器特有               | 作用                    |
| -------------------------- | ----------------------- |
| `reverse_iterator`         | 逆序迭代器类型          |
| `const_reverse_iterator`   | `const` 逆序迭代器类型  |
| `c.rbegin()`, `c.rend()`   | 获取逆向迭代器          |
| `c.crbegin()`, `c.crend()` | 返回 `const` 逆向迭代器 |

`std::forward_list` 不适用反向迭代器。

`const` 类型的迭代器一定是 `const` 类型的，非 `const` 类型可以用 `c` 开头的函数得到 `const` 迭代器。

### 获取大小

| 容器大小       | 作用                              | 返回                        |
| -------------- | --------------------------------- | --------------------------- |
| `c.size()`     | 大小（`std::forward_list` 不支持）| `std::container::size_type` |
| `c.empty()`    | 是否为空                          | `bool`                      |
| `c.max_size()` | 可保存的最大元素数                | `std::container::size_type` |

## 迭代器

一个迭代器范围指的是 `[begin, end)`。

注意：迭代器比较一般只用 `!=`，因为不是所有迭代器都定义了 `<` 操作符。

## 容器初始化

- 使用容器拷贝初始化另一个容器时 `T v1(v2)`，容器类型和元素类型必须完全匹配（如 `int` 和 `long long` 不匹配）
- 使用迭代器初始化则没关系

使用列表初始化可以不指定大小。

``` cpp
std::vector<const char*> articles = {"a", "an", "the"};
```

### `std::array`

`std::array` 的初始化必须指定大小。

``` cpp
std::array<int, 10> arr;
std::array<int, 10>::size_type i;
```

- `std::array` 不支持构造函数
- `std::array` 内部元素会被值初始化，因此要保证类型有默认构造函数（和数组一样）
- `std::array` 可以进行拷贝和赋值操作，但是要求元素类型和容器大小一样（和数组不同）
- `std::array` 也不支持花括号赋值（`a = {0}`）与 `assign()`

## 赋值

赋值会使得迭代器、引用、指针失效。

赋值操作要求容器类型和元素类型完全一致；`assign()` 不要求。

## `swap()`

- `std::array`
  - 对于 `std::array` 使用 `swap()` 会真正交换元素，效率可能很低
  - 交换之后指针/引用/迭代器仍指向原来的容器

- `std::string`：`swap()` 为常数时间，交换后指针/引用/迭代器都会失效

- 其它容器：`swap()` 为常数时间，交换后指针/引用/迭代器也会一起交换

最好统一使用泛型版本的 `std::swap()`。

## 关系操作

- 所有容器都支持 `==` 和 `!=`
- 除了无序关联容器外都支持 `<` 等比较运算符
- 比较的两个容器必须是同一种元素类型的同种容器

元素之间的比较要求定义 `==`，若要比较大小则必须定义 `<`。

# 顺序容器

## 插入元素

| 操作                    | 作用                               | 返回                                         |
| ----------------------- | ---------------------------------- | -------------------------------------------- |
| `c.push_back(t)`        | 在尾部插入 `t`                     | `void`                                       |
| `c.emplace_back(args)`  | 在尾部从 `args` 构造               | `void`                                       |
| `c.push_front(t)`       | 在头部插入 `t`                     | `void`                                       |
| `c.emplace_front(args)` | 在头部从 `args` 构造               | `void`                                       |
| `c.insert(p, t)`        | 在迭代器 `p` 前插入 `t`            | 指向插入元素的迭代器                         |
| `c.emplace(p, args)`    | 在迭代器 `p` 前从 `args` 构造      | 指向插入元素的迭代器                         |
| `c.insert(p, n, t)`     | 在迭代器 `p` 前插入 `n` 个 `t`     | 指向第一个插入元素的迭代器，若未插入返回 `p` |
| `c.insert(p, b, e)`     | 在迭代器 `p` 前插入区间 `[b, e)`   | 同上                                         |
| `c.insert(p, il)`       | 在迭代器 `p` 前插入初始化列表 `il` | 同上                                         |

以上操作都不支持 `std::array`。

- `std::forward_list` 有专属的 `insert()` 和 `emplace()`，没有 `push_back()` 和 `emplace_back()`
- `std::vector` 和 `std::string` 不支持 `push_front()` 和 `emplace_front()`

向 `std::vector`，`std::string`，`std::deque` 中插入元素会使原有迭代器失效。

利用 `insert()` 的返回值，可以在一个特定的位置不断插入元素。

``` cpp
std::list<std::string> lst;
auto iter = lst.begin();

while (std::cin >> word) {
    iter = list.insert(iter, word); // 反复在头部插入
}
```

### `emplace()`

`emplace()` 与 `push()` / `insert()` 的区别在于，前者构造对象，后者拷贝对象。

``` cpp
c.emplace_back("978-0590353403", 25, 15.99);
c.push_back(Sales_data("978-0590353403", 25, 15.99))
```

## 访问元素

访问之前一定要保证容器非空！

- 所有顺序容器都有 `front()` 成员函数，返回头元素的引用，等价于 `*c.begin()`
- 除了 `std::forward_list` 之外都有 `back()` 成员函数，返回尾元素的引用，等价于 `*--c.end()`

`c.front()` 等价于 `*c.begin()`，`c.end()` 等价于 `*--c.end()`

`std::forward_list` 的迭代器不能用 `--` 运算，`list` 的迭代器不能用 `+=` 和 `-=`。

| 访问元素                | 作用                                                                          |
| ----------------------- | ----------------------------------------------------------------------------- |
| `at()`, `[]`            | 访问某个位置的引用（`std::vector`, `std::string`, `std::deque`, `std::array`） |
| `c.front()`, `c.back()` | 返回首尾元素的引用（`std::forward_list` 不能用 `back()`）                      |

使用 `[]`、`front()`、`back()` 访问越界是 UB 行为，使用 `at()` 访问越界会抛异常 `std::out_of_range`。

## 删除元素

删除元素一定要注意性能和元素是否存在！

| 操作            | 作用                      | 返回                         |
| --------------- | ------------------------- | ---------------------------- |
| `c.pop_back()`  | 删除尾部元素              | `void`                       |
| `c.pop_front()` | 删除头部元素              | `void`                       |
| `c.erase(p)`    | 删除迭代器 `p` 指向的元素 | 被删除元素后一个元素的迭代器 |
| `c.erase(b, e)` | 删除区间 `[b, e)` 的元素  | 同上                         |
| `c.clear()`     | 清空                      | `void`                       |

- `std::deque` 删除中间位置的元素使迭代器失效

- `std::vector`、`std::string` 会使删除位置后的迭代器失效

- `std::forward_list` 有特殊的 `erase()`，不支持 `pop_back()`

- `std::vector`、`std::string` 不支持 `pop_front()`

用循环删除元素时，需要接受函数返回的迭代器。

``` cpp
// 删除 std::list 中所有奇数
std::list<int> lst;
auto beg = lst.begin();
while (beg != lst.end()) {
    if (*beg % 2) beg = lst.erase(beg);
    else ++beg;
}
```

## `std::forward_list`

`std::forawrd_list` 没有定义 `insert()`, `emplace()`, `erase()`; 而用
`insert_after()`, `emplace_after()`, `erase_after()` 代替，而且还定义了
`before_begin()` 首前迭代器来操纵首元素。（因为只能访问后继）

| 操作                         | 作用                           | 返回                                       |
| ---------------------------- | ------------------------------ | ------------------------------------------ |
| `lst.before_begin()`         | 首前迭代器                     |                                            |
| `lst.cbefore_begin()`        | 同上                           |                                            |
| `lst.insert_after(p, t)`     | 在迭代器 `p` 后插入 `t`        | 插入元素的迭代器                           |
| `lst.insert_after(p, n, t)`  | 在迭代器 `p` 后插入 `n` 个 `t` | 最后一个插入元素的迭代器，若未插入返回 `p` |
| `lst.insert_after(p, b, e)`  | 在迭代器 `p` 插入区间 `[b, e)` | 同上                                       |
| `lst.emplace_after(p, args)` | 在迭代器 `p` 后构造            | 同上                                       |
| `lst.erase_after(p)`         | 删除 `p` 指向的元素            | 被删除元素的后一个元素的迭代器             |
| `lst.erase_after(b, e)`      | 删除区间 `[b,e)`               | 同上                                       |

在操作 `std::forward_list` 的迭代器时，要注意当前元素的前驱。

``` cpp
// 删除一个 std::forward_list 中所有的奇数
std::forward_list<int> flst = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
auto prev = flst.before_begin();
auto cur = flst.begin();
while (cur != flst.end()) {
    if (*cur % 2) cur = flst.erase_after(prev); // 注意此时 cur 到了下一个元素，prev 仍然是 cur 的前驱
    else prev = cur++;
}
for (auto i : flst) cout << i << " ";
```

## 改变容器大小

`std::array` 不支持 `resize()`。

若变大则会添加新元素（值初始化），若变小则会抛弃尾部元素。

| 操作             | 作用                     | 返回   |
| ---------------- | ------------------------ | ------ |
| `c.resize(n)`    | 调整大小                 | `void` |
| `c.resize(n, t)` | 调整大小，新元素都为 `t` | `void` |

`resize()` 也有可能影响迭代器！

## 容器操作对指针/引用/迭代器的影响

### 插入元素

- `std::vector` / `std::string`：若存储空间重新分配则都失效；否则在插入元素之前的有效，插入元素之后的无效
- `std::deque`：中间位置插入则都失效；插入首尾则迭代器失效，引用/指针不失效
- `std::list` / `std::forward_list`：始终有效

### 删除元素

- `std::vector` / `std::string`：删除的元素之前的有效，之后的无效
- `std::deque`：中间位置删除则都失效；删除尾元素则尾后迭代器失效
- `std::list` / `std::forward_list`：始终有效

### 在循环中修改容器

如果使用的是 `insert()` / `erase()`，应该利用返回的迭代器。

使用尾后迭代器时应该直接用 `c.end()` 获取，而不是事先保存好一个 `end`，因为对容器的操作一定会使尾后迭代器失效。

``` cpp
auto beg = v.begin();
while (beg != v.end()) { // 注意这里
    ++begin;
    begin = v.insert(begin, 42);
    ++begin;
}
```

### 对比 `std::vector` / `std::list` / `std::forward_list`

将序列中的奇数复制一份，偶数删除：

- `std::vector`：注意操作之后一定要利用返回的迭代器

``` cpp
std::vector<int> v{1, 2, 3, 4, 5, 6, 7, 8, 9, 0};
auto beg = v.begin();
while (beg != v.end()) {
    if (*beg % 2) beg = v.insert(beg, *beg), ++beg, ++beg;
    else beg = v.erase(beg);
}
```

- `std::list`：限制最少

``` cpp
std::list<int> lst{1, 2, 3, 4, 5, 6, 7, 8, 9, 0};
auto beg = lst.begin();
while (beg != lst.end()) {
    if (*beg % 2) lst.insert(beg, *beg), ++beg;
    else beg = lst.erase(beg);
}
```

- `std::forward_list`：要保存 `prev`

``` cpp
std::forward_list<int> flst{1, 2, 3, 4, 5, 6, 7, 8, 9, 0};
auto beg = flst.begin(), prev = flst.before_begin();
while (beg != flst.end()) {
    if (*beg % 2) flst.insert_after(prev, *beg), prev = beg++;
    else beg = flst.erase_after(prev);
}
```

# `std::vector` 容器大小管理

| 容器大小管理        | 作用                                   | 返回   |
| ------------------- | -------------------------------------- | ------ |
| `c.shrink_to_fit()` | 将 `capacity()` 调整为 `size()` 的大小 | `void` |
| `c.capacity()`      | 若不重新分配空间最多可以保存多少元素   | `void` |
| `c.reserve(n)`      | 分配至少 `n` 个元素的空间              | `void` |

当所需空间不足时，`reserve()` 函数才有作用。

`std::deque`, `std::vector`，`std::string` 都可以使用 `shrink_to_fit()`，但是不保证能退回空间。

- `reserve()` 和 `resize()` 的区别：`resize()` 会改变元素数量

每次 `std::vector` 重新分配空间几乎都是当前空间的翻倍。

# `std::string` 操作

## 构造函数

| 构造方法                        | 作用                                              |
| ------------------------------- | ------------------------------------------------- |
| `std::string s(cp, n)`          | `s` 是字符数组 `cp` 前 `n` 个元素的拷贝           |
| `std::string s(s2, pos2)`       | `s` 是 `std::string` 的 `s2` 从 `pos2` 开始的拷贝 |
| `std::string s(s2, pos2, len2)` | 同上，拷贝 `len2` 个字符，最多拷贝到尾部为止      |

从 `std::string` 中拷贝时，如果 `pos2 > s2.size()`，会抛出 `std::out_of_range` 异常。

如果用 `std::string s(cp)` 初始化结尾一定要有 `\0`。

## `substr()`

- `s.substr(pos2)`：`s` 从 `pos2` 到尾部的拷贝
- `s.substr(pos2, len2)`：`s` 从 `pos2` 开始拷贝 `len2` 个元素，最多拷贝到尾部为止

同样，如果 `pos2 > s.size()` 会抛出 `std::out_of_range` 异常。

## 增删操作

除了通用的操作，`std::string` 对于 `insert()`，`assign()` 和 `erase()` 还支持更多操作，并且支持用 `append()` 来附加子串和用 `replace()` 进行替换。

| 函数                     | 作用                                                                           |
| ------------------------ | ------------------------------------------------------------------------------ |
| `s.insert(pos, args)`    | 在 `pos` 之前插入 `args` 指定的字符，`pos` 可以是迭代器，返回值取决于 `pos`    |
| `s.erase(pos, len)`      | 删除 `pos` 开始的 `len` 个字符，如果 `pos` 被省略则删除到尾部，返回 `s` 的引用 |
| `s.assign(args)`         | 将 `s` 替换为 `args` 指定的字符，返回 `s` 的引用                               |
| `s.append(args)`         | 将 `args` 追加到 `s`，返回 `s` 的引用                                          |
| `s.replace(range, args)` | 将 `range` 替换为 `args` 指定的字符，返回 `s` 的引用                           |

- `s.insert(pos, args)` 的 `pos` 如果是下标，那么返回 `s` 的引用；如果是迭代器，返回指向插入的第一个字符的迭代器
- `s.replace(range, args)` 的 `range` 可以是下标和长度（`pos, len`）或者一对迭代器区间 `[b, e)`

`args` 可以是以下几种：

- `(str)`：`std::string`
- `(str, pos, len)`：\=std::string=，位置，长度
- `(cp, len)`：字符数组和长度
- `(cp)`：字符数组
- `(n, c)`：`n` 为数字，`c` 为字符
- `(b2, e2)`：迭代器区间
- `{}`：初始化列表

`assign()` 和 `append()` 支持所有形式的 `args`，其它函数的支持度如下：

| 参数              | `replace(pos, len, args)` | `replace(b, e, args)` | `insert(pos, args)` | `insert(iter, args)` |
| ----------------- | ------------------------- | --------------------- | ------------------- | -------------------- |
| `(str)`           | √                         | √                     | √                   |                      |
| `(str, pos, len)` | √                         |                       | √                   |                      |
| `(cp, len)`       | √                         | √                     | √                   |                      |
| `(cp)`            | √                         | √                     |                     |                      |
| `(n, c)`          | √                         | √                     | √                   | √                    |
| `(b2, e2)`        |                           | √                     |                     | √                    |
| `{}`              |                           | √                     |                     | √                    |

规律：

- `assign()` 和 `append` 不用指定原串的位置
- `replace()` 可以选择“位置 + 长度”或者两个迭代器
- `insert()` 可以选择一个下标或者一个迭代器，新元素都会插入到指定位置之前
- 添加的字符可以来自 `std::string`、字符数组、花括号组成的字符列表、字符 + 计数值。对于前两个可以指定拷贝部分还是全部。

## 搜索

`std::string` 有六种搜索函数，每种函数的参数可以是四种形式。

搜索函数返回类型为 `std::string::size_type`，表示匹配位置的下标。如果搜索失败返回一个 `const static unsigned` 成员 `std::string::npos`，默认为 `-1`（即无穷大）。

### 搜索函数

| 函数                        | 作用                                 |
| --------------------------- | ------------------------------------ |
| `s.find(args)`              | 查找第一次出现                       |
| `s.rfind(args)`             | 同上，从右边开始找                   |
| `s.find_first_of(args)`     | 查找 `args` 中任意一个字符第一次出现 |
| `s.find_last_of(args)`      | 同上，从右边开始找                   |
| `s.find_first_not_of(args)` | 查找第一个不在 `args` 中出现的字符   |
| `s.find_last_not_of(args)`  | 同上，从右边开始找                   |

参数有四种形式

- `(c, pos)`：从 `pos` 开始找字符 `c`, `pos` 默认为 `0`
- `(s2, pos)`：同上，`s2` 为 `std::string`
- `(cp, pos)`：同上，`cp` 为字符数组
- `(cp, pos, n)`：从 `s` 中 `pos` 位置开始找数组 `cp` 的前 `n` 个字符，`pos` 和 `n` 无默认值

搜索都是大小写敏感的。

### 循环搜索

``` cpp
std::string::size_type pos = 0;
while((pos = name.find_first_of(number, pos))
      != std::string::npos) {
    std::cout << pos << std::endl;
    ++pos; // 这个很重要
}
```

## 比较函数

字符串的比较函数 `s1.compare()` 可以接受 `6` 种参数：

- `(s2)`：比较 `std::string` 的 `s2`
- `(pos1, n1, s2)`：将 `s1` 从 `pos1` 开始的前 `n1` 个字符和 `s2` 比较
- `(pos1, n1, s2, pos2, n2)`：同上，和 `s2` 从 `pos2` 开始的前 `n2` 个字符比较
- `cp`：和字符数组比较
- `(pos1, n1, cp)`：将 `s1` 从 `pos1` 开始的前 `n1` 个字符和 `cp` 比较 `s`
- `(pos1, n1, cp, n2)`：同上，和 `cp` 从 `pos2` 开始的前 `n2` 个字符比较

等于返回 `0`，小于返回负数，大于返回正数。

## 数值转换

| 函数                  | 作用                                                    |
| --------------------- | ------------------------------------------------------- |
| `std::to_string(val)` | 将 `val` 转换为 `std::string`, `val` 可以是整数或浮点数 |
| `std::stoi(s, p, b)`  |                                                         |
| `std::stol(s, p, b)`  | 同上，返回 `long`                                       |
| `std::stoul(s, p, b)` | 同上，返回 `unsigned long`                              |
| `std::stoll(s, p, b)` | 同上，返回 `long long`                                  |
| `std::stoull`         | 同上，返回 `unsigned long long`                         |
| `std::stof(s, p)`     |                                                         |
| `std::stod(s, p)`     | 同上，返回 `double`                                     |
| `std::stold(s, p)`    | 同上，返回 `long double`                                |

用 `to_string()` 时小整数会进行提升。

- 如果 `std::string` 不能转换成数值，会抛出 `std::invalid_argument` 异常
- 如果转换得到的数值不能用任何类型表示，会抛出 `std::out_of_range` 异常

数值转换的第一个字符必须是符号（`+`、`-`）或数字，并且转换会在第一个非数字字符处停止。数字可以是以下几种：

- 普通数字
- `0x` 或 `0X` 开头的十六进制数
- `.` 开头表示浮点数
- 包含 `e` 和 `E` 表示科学计数法
- 包含字母表示其它进制中大于 `10` 的数

# 容器适配器

适配器可以接受一种容器，并基于此实现特殊功能。

顺序适配器有 `std::stack`、`std::priority_queue`、`std::queue`。

适配器对底层实现容器有要求：

- `std::stack` 要去容器有 `push_back()`、`pop_back()`、`back`，即除 `std::array` 和 `std::forward_list` 之外的所有容器
- `std::queue` 要求容器有 `push_back()`、`pop_front()`、`back()`、`front()`，即 `std::list` 和 `std::deque`
- `std::priority_queue` 要求容器有 `front()`、`push_back()`、`pop_back()`，可随机访问，即 `std::vector` 和 `std::deque`

## 定义适配器

适配器的第二个参数用来指定底层实现。

``` cpp
std::stack<std::string, std::vector<std::string>> str_stk;
```

## 适配器通用成员

| 成员             | 作用                         |
| ---------------- | ---------------------------- |
| `size_type`      | 容器大小，无符号整数类型     |
| `value_type`     | 元素类型                     |
| `container_type` | 实现适配器的底层容器的类型   |
| `A a;`           | 创建空适配器                 |
| `A a(c);`        | 适配器 `a` 为容器 `c` 的拷贝 |
| 关系运算符       | 适配器支持所有的关系运算符   |
| `a.empty()`      |                              |
| `a.size()`       |                              |
| `a.swap(b)`      |                              |
| `swap(a, b)`     |                              |

## `std::stack`

`std::stack` 默认基于 `std::deque`，也可以用 `std::list` 或 `std::vector`。

| 操作              | 作用                   |
| ----------------- | ---------------------- |
| `s.pop()`         | 删除顶部元素，不返回值 |
| `s.push(item)`    |                        |
| `s.emplace(args)` | 压入新元素             |
| `s.top()`         | 返回顶部元素           |

## `std::queue` / `std::priority_queue`

`std::queue` 默认基于 `std::deque`，也可以用 `std::list`。

`std::priority_queue` 默认基于 `std::vector`，也可以用 `std::deque`。

| 操作              | 作用                                                  |
| ----------------- | ----------------------------------------------------- |
| `q.pop()`         | 弹出队首                                              |
| `q.front()`       | 返回队首                                              |
| `q.back()`        | 返回队尾（只适用于 `std::queue`）                      |
| `q.top()`         | 返回最高优先级的元素（只适用于 `std::priority_queue`） |
| `q.push(item)`    |                                                       |
| `q.emplace(args)` |                                                       |
