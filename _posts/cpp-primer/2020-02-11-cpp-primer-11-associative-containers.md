---
layout: "post"
title: "「C++ Primer」 11 Associative Containers"
subtitle: "关联型容器"
author: "roife"
date: 2020-02-11

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 关联容器

关联容器能实现高效的元素查找和访问，其中主要的是 `map` 和 `set`。STL 提供了八个关联容器，区别在于

- `map` 还是 `set`
- 是否允许关键字重复（`multi-`）
- 按顺序保存，还是无序（哈希）保存（`unordered-`，`unordered_multi-`）

其中，

- `std::map` 和 `std::multimap` 定义在头文件 `map` 中
- `std::set` 和 `std::multiset` 定义在头文件 `set` 中
- 无序容器定义在 `std::unordered_map` 和 `std::unordered_set` 中

关联容器不支持顺序容器中和位置有关的 `push_back` 操作，也不接受“一个元素值 + 一个数量值”（如初始化 `n` 个 `t`）的操作。

关联容器的迭代器是双向的。

# 有序容器

## 关联容器定义

- 定义 `std::map` 要指明关键字与值的类型，初始化要使用 `{key, value}` 的形式
- 定义 `std::set` 只要指明关键字类型

``` cpp
std::map<std::string, std::string> authors = { {"Joyce", "James"}, {"Austen", "Jane"}};
std::set<std::string> exclude = {"the" "but" "and"};

// set 也支持类似于顺序容器的两种构造函数
std::set<std::string> set1(exclude); // 拷贝已有 set
std::set<std::string> set2(v.begin(), v.end()); // 用序列迭代器初始化
```

## 关键字类型要求

关联容器对关键字类型有要求：一般使用 `<` 比较关键字，或者提供一个比较用的谓词（并且要提供谓词的类型）。

关键字的比较必须满足**严格弱序**：

- 两个元素不能同时小于对方
- 不等关系的传递性
- 若 `v1>=v2 && v2>=v1`，则 `v1=v2`，且等号有传递性

``` cpp
bool compareIsbn(const Sales_data &lhs, const Sales_data &rhs) { return lhs.isbn() < rhs.isbn; }

std::multiset<Sales_data, decltype(compareIsbn)*> bookstore(compareIsbn);
// 必须加上 * 表明是函数指针，类型也可以写成 bool(*)(const Sales_data&, const Sales_data&)
// 函数当参数传递时，会自动转换成函数指针，也可以写 &compareIsbn
```

## `std::pair` 类型

`std::pair` 类型定义在 `utility` 中，用来关联两个数据。

``` cpp
std::pair<std::string, size_t> word_count {"Hello", 2};
```

| 操作                      | 作用                                          |
| ------------------------- | --------------------------------------------- |
| `pair<T1, T2> p`          |                                               |
| `pair<T1, T2> p{v1, v2}`  |                                               |
| `pair<T1, T2> p={v1, v2}` |                                               |
| `make_pair(v1, v2)`       | 返回一个 `v1`, `v2` 组成的 `pair`             |
| `p.first`, `p.second`     | 访问成员                                      |
| `p1 op p2`                | 比较两个 pair，先比较第一个元素，再比较第二个 |

``` cpp
std::pair<std::string, int> process(const std::vector<int> &v) {
    if (!v.empty()) return { v.back(), v.back().size() }; // 也可以用 make_pair(v.back(), v.back().size())
    else return std::pair<std::string, int>(); // 用构造函数返回初始值
}
```

# 关联容器操作

## 关联容器类型

| 类型          | 含义                                                                                 |
| ------------- | ------------------------------------------------------------------------------------ |
| `key_type`    | 关键字的类型                                                                         |
| `mapped_type` | 关联类型（仅 `map`）                                                                 |
| `value_type`  | 对于 `set`，等于 `key_type`；对于 `map`，为 `std::pair<const key_type, mapped_type>` |

`std::map` 中每个元素都是一个 `std::pair`。

如对于 `std::map<A, B>`

- `key_type` 为 `A`
- `mapped_type` 为 `B`
- `value_type` 为 `std::pair<const A, B>`

## 关联容器迭代器

用关联容器遍历时，迭代器按照字典序升序排序。

一般不对关联容器使用泛型算法（关键字是 `const` 类型，而且按照关键字查值较慢），而用关联容器自定义的算法（但是可以当作算法的源序列）。

### `map` 的迭代器

解引用器的迭代器会得到一个 `value_type` 的 `std::pair`，应该用 `first`（`const` 类型）和 `second` 来取值。

``` cpp
std::map<std::string, size_t> word_count;
// ...

auto map_it = word_count.begin();
std::cout << map_it->first << " " << map_it->second << std::endl;
++map_it->second; // 不可以修改 map_it->first
```

### `set` 的迭代器

`set` 的迭代器是 `const` 的。

``` cpp
std::set<int> iset = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
auto set_it = iset.begin();

if(set_it != iset.end()) {
    *set_it = 42; // 非法
    std::cout << *set_it << std::endl;
}
```

## 插入元素

| 操作                 | 作用                                                                               |
| -------------------- | ---------------------------------------------------------------------------------- |
| `c.insert(v)`        | 插入元素，返回 `std::pair` 包含一个指向插入位置的迭代器和一个表示是否成功的 `bool` |
| `c.emplace(args)`    | 同上，构造元素                                                                     |
| `c.insert(b, e)`     | 插入迭代器区间 `[b, e)` 内的元素（类型为 `value_type`），函数返回 `void`            |
| `c.insert(il)`       | 同上，插入花括号列表                                                               |
| `c.insert(p, v)`     | `p` 为提示，返回指向插入位置的迭代器                                               |
| `c.emplace(p, args)` | 同上，构造元素                                                                     |

- 对于 `map` 或 `set` 只有元素的关键字不在 `c` 内的时候才能插入成功（即以第一次插入为准）
- 对于 `multimap` 或 `multiset` 总是可以插入成功，因此只返回新元素的迭代器
- 向 `map` 中插入的元素 `v` 必须是一个 `std::pair`，如 `word_count.insert({word, 1})` 或 `word_count.insert(std::make_pair(word, 1))`

``` cpp
std::map<std::string, size_t> word_count;
std::string word;

while(std::cin >> word) {
    auto ret = word_count.insert({word, 1}); // ret 的类型为 std::pair<std::map<std::string, size_t>::iterator, bool>
    if(!ret.second) ++ret.first->second;     // 若存在则数量加一，注意运算优先级
    // 也可以直接这么写：++word_count.insert({word, 0}).first->second;
}
```

## 删除元素

| 操作            | 作用                                       | 返回                                        |
| --------------- | ------------------------------------------ | ------------------------------------------- |
| `c.erase(k)`    | 删除所有关键字为 `k` 的元素                | 删除的数量（对 `map` 或 `set` 来说是 `0/1`） |
| `c.erase(p)`    | 删除迭代器 `p` 指向的元素，`p` 须在 `c` 中 | `p` 元素后一个元素的迭代器或 `c.end()`      |
| `c.erase(b, e)` | 删除迭代器区间 `[b, e)`                    | 返回迭代器 `e`                              |

## 下标操作（`map`）

| 操作      | 作用                                                            |
| --------- | --------------------------------------------------------------- |
| `c[k]`    | 返回 `k` 对应的值，若 `k` 不存在则创建一个并进行值初始化        |
| `c.at(k)` | 访问 `k` 对应的值，若 `k` 不存在，抛出 `std::out_of_range` 异常 |

- 下标操作只适用于非 `const` 的 `std::map` 和 `std::unordered_map`

使用下标时返回一个 `mapped_type` 类型，解引用迭代器则返回 `value_type`。

## 访问元素

| 操作               | 作用                                                                        |
| ------------------ | --------------------------------------------------------------------------- |
| `c.find(k)`        | 返回迭代器指向第一个关键字为 `k` 的元素，不存在则返回尾后迭代器             |
| `c.count(k)`       | 返回关键字为 `k` 的元素数量                                                 |
| `c.lower_bound(k)` | 返回迭代器指向第一个关键字 `>=k` 的元素                                     |
| `c.upper_bound(k)` | 返回迭代器指向第一个关键字 `>k` 的元素                                      |
| `c.equal_range(k)` | 返回迭代器 `pair` 指向关键字等于 `k` 的元素范围。若不存在则都都是 `c.end()` |

- `lower_bound()` 和 `upper_bound()` 不适用于无序容器
- 使用下标访问会插入不存在的元素，可以用 `find()` 替代

## 在 `std::multimap` 与 `std::multiset` 中遍历

### 直接用迭代器

在 `multimap`、`multiset` 想要打印元素时，相同关键字的元素相邻存储。

``` cpp
std::string search_item("Alain de Botton");
auto entries = authors.count(search_item);
auto iter = authors.find(search_item);

while(entries--) {
    std::cout << iter++->second << std::endl;
}
```

### `lower_bound()` 与 `upper_bound()`

也可以用 `lower_bound()` 与 `upper_bound()` 来实现。

- 当元素存在时，`lower_bound()` 返回第一个位置，`upper_bound()` 返回最后一个元素的尾后迭代器
- 当元素不存在时，则都返回能插入的位置

``` cpp
for (auto beg = authors.lower_bound(search_item), end = authors.upper_bound(search_item);
     beg != end; ++beg)
    std::cout << beg->second << std::endl;
```

### `equal_range()`

`c.equal_range(v)` 返回一个 `std::pair`。

- 如果关键字存在，则分别为第一个匹配元素的迭代器和最后一个匹配元素的尾后迭代器
- 如果关键字不存在，则两个迭代器都返回可插入位置

``` cpp
for (auto pos = authors.equal_range(search_item);
     pos.first != pos.second; ++pos.first)
    std::cout << pos.first->second << std::endl;
```

注意直接用 `mp[key] = value` 和 `mp.insert({key, value})` 的区别，前者保存的是最后一次插入的版本，后者保存的是第一次插入的版本。

# 无序容器

- 无序容器用哈希函数和 `==` 来组织元素，不用 `<`，通常情况下性能更好
- 有序容器的大部分操作无序容器都能用（除了 `lower_bound()` 之类的）
- 无序容器的迭代器访问时不会按照字典序

## 管理桶

无序容器会将相同哈希值的元素存在同一个桶里，因此其性能依赖于哈希函数的质量和桶的数量。

### 桶操作

| 桶操作                 | 作用                    | 返回                                     |
| ---------------------- | ----------------------- | ---------------------------------------- |
| `c.bucket_count()`     | 桶的数量                | `std::unordered_container<T>::size_type` |
| `c.max_bucket_count()` | 最多容纳多少桶          | 同上                                     |
| `c.bucket_size(n)`     | 第 `n` 个桶有多少元素   | 同上                                     |
| `c.bucket(k)`          | 关键字 `k` 存在第几个桶 | 同上                                     |

### 桶迭代器

| 桶迭代器                   | 作用               |
| -------------------------- | ------------------ |
| `local_iterator`           | 桶迭代器类型       |
| `const_local_iterator`     | `const` 版本迭代器 |
| `c.begin(n)`, `c.end(n)`   | 桶 `n` 的迭代器    |
| `c.cbegin(n)`, `c.cend(n)` | 同上               |

### 重组存储

| 哈希策略              | 作用                                                                          | 返回          |
| --------------------- | ----------------------------------------------------------------------------- | ------------- |
| `c.load_factor()`     | 每个桶的平均数量（`float`）                                                    | `float (0~1)` |
| `c.max_load_factor()` | `c` 试图维护的平均桶大小                                                      | `float`       |
| `c.rehash(n)`         | 重组存储，使得 `bucket_count >= n` 且 `bucket_count > size/max_load_factor()` | `void`        |
| `c.reserve(n)`        | 视情况进行 `rehash()`，使可容纳 `n` 个元素而不会 `rehash()`                   | `void`        |

- 当 `load_factor() > max_load_factor` 时，会添加新的桶
- `rehash()` 会重选模素数使 `p > n`
- `reserve()` 等价于 `rehash(n/max_load_factor())`

## 自定义哈希函数

无序容器使用 `std::hash<key_type>` 来生成对象的哈希值。标准库为内置类型和一些标准库类型（`std::string`，智能指针等）提供了 hash 模板，但是也可以自定义哈希函数。

格式为 `std::unordered_container<Type, Hasher, EqualOp>` 或 `std::unordered_container<Type, Hasher>`。

``` cpp
size_t hasher(const Sales_data &sd) { return hash<std::string>() (sd.isbn()); } // 定义 hash 函数
bool eqOp(const Sales_data &lhs, const Sales_data &rhs) { return lhs.isbn() == rhs.isbn(); } // 定义 == 操作

using SD_multiset = std::unordered_multiset<Sales_data, decltype(hasher)*, decltype(eqOp)*>;
SD_multiset bookstore(42, hasher, eqOp); // 分别是桶大小，hash 函数指针和比较函数指针

// 如果定义了 == 操作，也可以只重载哈希函数
std::unordered_multiset<Sales_data, decltype(hasher)*> bookstore2(42, hasher);
```
