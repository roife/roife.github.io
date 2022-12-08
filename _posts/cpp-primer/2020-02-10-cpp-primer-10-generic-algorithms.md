---
layout: "post"
title: "「C++ Primer」 10 Generic Algorithms"
subtitle: "泛型算法"
author: "roife"
date: 2020-02-10

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 泛型算法

泛型算法运行于迭代器之上，不涉及容器操作，不能改变容器。

# 常用算法

## 只读算法

不会改变元素，推荐用 `cbegin`、`cend`。

- `std::find(cbeg, cend, val)`：寻找 `val`，返回找到的迭代器，找不到则返回 `cend`
- `std::count(cbeg, cend, val)`：统计 `val` 出现次数
- `std::accumulate(cbeg, cend, val)`：累加，初始值为 `val`（注意字符数组或字符串字面值要先转换成 `std::string`)

返回值类型与 `val` 相同，因此要注意类型转换！如 `std::accumulate(v.cbegin(), v.cend(), static_cast<double>(0))`

- `std::equal(cbeg1, cend1, beg2)`：比较序列。（序列 `2` 必须至少和序列 `1` 一样长）

一般接受两个序列且第二个序列用单一迭代器表示，要求第二个序列长度至少和第一个一样长。

## 写容器的算法

算法写数据时不会检查，因此要小心原来容器能不能放得下。

- `std::fill(beg, end, val)`：充填为 `val`
- `std::fill_n(beg, n, val)`：写入 `n` 个 `val`

``` cpp
std::vector<int> v;
std::fill_n(v.begin(), 10, 0); // 错误！v 可能放不下
```

- `std::copy(cbeg1, cend1, beg2)`：将元素拷贝到 `beg2` 处（要保证能放下），返回 `beg2` 中尾后元素的迭代器
- `std::replace(beg1, beg2, val1, val2)`：将 `val1` 替换成 `val2`
- `std::replace_copy(cbeg1, cend1, beg2, val1, val2)`：将结果保存在 `beg2` 处

### `std::back_inserter`

定义在头文件 `iterator` 中。

`std::back_inserter` 接受一个容器的引用，返回一个插入迭代器，向其赋值会向容器 `push_back()` 元素。

``` cpp
std::vector<int> v;
auto it = back_inserter(v); // 类型为 std::back_insert_iterator<std::vector<int>>
*it = 42; // v.push_back(42);
```

`std::back_inserter` 可以和泛型算法结合，如 `std::fill_n(std::back_inserter(v), 10, 0)`，每次向迭代器 `*it` 赋值，都等价于 `push_back()`。

## 重排容器的算法

- `std::sort(beg, end)`：排序（从小到大）
- `std::unique(beg, end)`：去除重复（要求先排序），把元素挪到尾部，返回新序列的尾后迭代器

``` cpp
void elimDups(std::vector<std::string> &words) {
    std::sort(words.begin(), words.end());
    auto end_unique = std::unique(words.begin(), words.end());
    words.erase(end_unique, words.end());
}
```

# 定制函数

## 向算法传递谓词

谓词是一个可调用的表达式，并返回一个用于 `if` 表达式的值，分为一元谓词与二元谓词。谓词必须能接受容器输入的元素，要求类型可转换。

- `std::sort(beg, end, pred)`：用 `pred` 来代替 `<` 比较元素

``` cpp
bool isShorter(const std::string &s1, const std::string &s2) {
    return s1.size() < s2.size();  // 建议用 const Type&
}
```

- `std::stable_sort(beg, end, pred)`：在排序的同时，相同大小的元素按照原顺序
- `std::partition(beg, end, pred)`：重新排序，满足谓词的排在前半部分，不满足的排在后半部分，返回前半部分的尾后迭代器
- `std::find_if(beg, end, pred)`：返回第一个使谓词为真的迭代器（找不到返回尾后迭代器）
- `for_each(beg, end, pred)`：对所有元素都执行 `pred` 操作
- `transform(beg1, end1, beg2, pred)`：将序列用 `pred` 转换后存在 `beg2` 处（`beg1`, `beg2` 可相同）
- `count_if(beg, end, pred)`：返回范围内使 `pred` 为真的元素数

## lambda 表达式

谓词对于参数有严格要求，不利于代码复用，此时可以用 lambda 表达式。

lambda 表达式的形式为 `[capture list] (parameter list) -> return type {function body}`

- 参数列表和返回类型可以省略
- 必须包含捕获列表和函数体
- 省略返回类型时，如果函数体只是一个 return 表达式，则返回类型会自动推断，否则返回值为 `void`
- lambda 表达式可以像函数一样调用，在对象被创建的时候初始化
- 任意两个 lambda 表达式（即使结构相同）的类型都不同

``` cpp
auto f = [] { return 42; };
std::cout << f() << std::endl;

auto wc = std::find_if(v.begin(), v.end(),
                       [sz](const std::string &a) { return a.size > sz; });
```

### 参数

lambda 不能有默认参数。

### 捕获

- 对于全局变量或 `static` 变量，lambda 表达式可以直接使用

- 对于局部变量，必须捕获后才能使用

- 值捕获 `[names]`（前提是变量可拷贝）

``` cpp
void fcn1() {
    size_t v1 = 42;
    auto f = [sz] { return sz; };
    sz = 0;
    auto j = f(); // 42
}
```

值捕获与值形参类似，区别在于 lambda 表达式会在创建时拷贝变量，而非调用时拷贝。

- 引用捕获
  : `[&names]`

``` cpp
void fcn2() {
    size_t v1 = 42;
    auto f2 = [&sz] { return sz; };
    v1 = 0;
    auto j = f(); // 0
}

std::find_if(v.begin(), v.end(),
             [&os, c](const std::string &s) { os << s << c; });
```

引用捕获类似于引用传参，必须保证 lambda 表达式调用时局部变量存在。

- 隐式捕获：`[&]`、`[=]`、`[&, identifier_list]`、`[=, &identifier_list]`

编译器自动推断捕获的变量。其中 `=` 表示值捕获，`&` 表示引用捕获。

``` cpp
wc = std::find_if(v.begin(), v.end(),
                  [=](const std::string &s){ return s.size() > sz; }); // 自动捕获值引用
```

也可以混用值捕获与引用捕获

``` cpp
std::for_each(v.begin(), v.end(),
              [&, c](const std::string &s) { return os << s << c; }); // c 值捕获，其他都引用捕获

std::for_each(v.begin(), v.end(),
              [=, &os](const std::string &s) { return os << s << c; }); // os 引用捕获，其他都值捕获
```

### 改变值传递参数值

- 值捕获的变量默认是 `const` 的，若要在 lambda 中修改，需用 `mutable` 修饰。（此时仍不会改变外面的变量，与引用捕获区分）

``` cpp
void fcn3() {
    size_t v1 = 42;
    auto f = [sz] () mutable { return v1 + 1; };
    auto j = f(); //
}
```

### 返回类型

编译器无法推断类型，且未指定类型时会产生编译错误。

``` cpp
std::transform(v.begin(), v.end(), v.begin(),
               [] (int i) -> int { if (i>=0) return i; else return -i; }); // 编译错误
```

## 参数绑定

有捕获列表的 lambda 可以用 `std::bind` 实现

`std::bind` 定义在头文件 `functional` 中，接受一个可调用对象，并生成新的可调用对象，格式为 `auto newCallable = bind(callable, arg_list)`。

`arg_list` 包含类似 `std::placeholders::_n` 的占位符，表示新函数的第 `n` 个参数，定义在 `std::placeholders` 中，也在头文件 `functional` 中。为了方便，可以用 `using namespace std::placeholders` 来避免重复写命名空间。

``` cpp
bool checkSize(const std::string &s, std::string::size_type sz) { return s.size() > sz; }

auto wc = std::find_if(v.being(), v.end(), std::bind(checkSize, std::placeholders::_1, sz)); // 等价于使用捕获列表的 lambda 表达式
```

### 绑定和重排参数

`std::bind` 会拷贝参数，占位符表示新函数的参数。

``` cpp
auto g = std::bind(f, a, b, _2, c, _1); // 把 g 的第一个参数给 f 的_1，第二个参数给 f 的_2
g(X, Y); // f(a, b, Y, c, X);
```

### `std::ref` 引用绑定

`std::bind` 的绑定过程中都是值绑定，对于引用绑定需要对参数用 `std::ref` 和 `std::cref`，都定义在 `functional` 中。

``` cpp
std::for_each(v.begin(), v.end(), std::bind(print, std::ref(os), _1, ' '));
```

# 再探迭代器

迭代器有五种：

- 插入迭代器
- 流迭代器
- 反向迭代器
- 移动迭代器

## 插入迭代器

给插入迭代器赋值相当于给容器插入元素。

| 操作                 | 作用               |
| -------------------- | ------------------ |
| `it = t`             | 在指定位置插入 `t` |
| `*it`, `++it`, `--t` | 无意义，返回 `it`  |

- `std::back_inserter(c)`：使用 `push_back()`（要求支持 `push_back()`)
- `std::front_inserter(c)`：使用 `push_front()`（要求支持 `push_front()`)
- `std::inserter(c, iter)`：使用 `insert()`，接受第二个参数（迭代器）表示位置，每次元素被插入到迭代器之前

``` cpp
std::copy(lst.cbegin(), lst.cend(), std::front_inserter(lst2));
std::copy(lst.cbegin(), lst.cend(), std::inserter(lst3, list3.begin()));
```

## 流迭代器

流迭代器可以用迭代器的方式操纵输入输出流，并且可以结合泛型算法使用。

### `std::istream_iterator`

- 创建流迭代器必须指明对象类型，且要求类型定义 `>>` 运算
- 创建时要绑定一个流，若不绑定则成为一个尾后值

``` cpp
std::istream_iterator<int> int_it(std::cin);
std::istream_iterator<int> int_eof; // 尾后值

std::ifstream in("afile");
std::istream_iterator<std::string> str_it(in);
```

| 操作                              | 作用                                                                              |
| --------------------------------- | --------------------------------------------------------------------------------- |
| `std::istream_iterator<T> in(is)` | 创建一个和流 `is` 绑定的迭代器                                                    |
| `std::istream_iterator<T> in_eof` | 创建一个值                                                                        |
| `in1==in2`，`in1!=in2`            | in1 与 in2 必须读取的是完全相同的类型，当绑定到相同的输入流时或都是尾后迭代器相等 |
| `*it`                             | 从流中读取值                                                                      |
| `in->mem`                         | `(*in).mem`                                                                       |
| `++in`, `in++`                    | 读取下一个值                                                                      |

`std::istream_iterator` 可以简化读取数据的操作。

``` cpp
// 用 istream_iterator 读取数字并存在 vector 中
std::istream_iterator<int> in_iter(cin), in_eof;
std::vector<int> v;
while (in_iter != in_eof) {
    v.push_back(*in_iter++);
}

// 或者直接写成初始化的形式
std::istream_iterator<int> in_iter(cin), in_eof;
std::vector<int> v(in_iter, in_eof);

// 将输入元素累加
std::istream_iterator<int> in_iter(cin), in_eof;
std::cout << std::accumulate(in_iter, in_eof, 0) << std::endl; // 不需要中间变量 v
```

标准允许 `std::istream_iterator` 采用 lazy evaluation，即迭代器在创建时不读入，使用时才读入。（两个流关联时要注意）

### `std::ostream_iterator`

| 操作                                   | 作用                                                                            |
| -------------------------------------- | ------------------------------------------------------------------------------- |
| `std::ostream_iterator<T> out(os)`     | 创建一个和流 `os` 绑定的迭代器                                                  |
| `std::ostream_iterator<T> out(os, ch)` | 创建一个和流 `os` 绑定的迭代器，每次输出时紧接着输出 `ch`（`ch` 是一个字符数组）|
| `out = val`                            | 将 `val` 输出到流（允许类型转换）                                                |
| `*out`, `++out`, `out++`               | 无意义，返回 `out`                                                              |

``` cpp
// 输出元素
std::ostream_iterator<int> out_iter(std::cout, " ");
for (auto e: vec) *out_iter++ = e; // 可以写成 out_iter++ = e，用解引用的方式一致性更强
std::cout << std::endl;

// 或者直接用泛型算法
std::copy(vec.begin(), vec.end(), out_iter);
std::cout << std::endl;
```

## 反向迭代器

反向迭代器从尾部到头部移动，`++it` 向前移动，`--it` 向后移动。

``` cpp
std::sort(v.rbegin(), v.rend()); // 从大到小排序
```

流迭代器和 `std::forward_list` 没有反向迭代器。

### `base()`

用 `base()` 可以把反向迭代器转换成普通迭代器：

``` cpp
std::string line = "FIRST, MIDDLE, LAST";
auto rcomma = std::find(line.crbegin(), line.crend(), ',');

std::cout << std::string(line.crbegin(), rcomma) << std::endl; // TSAL
std::cout << std::string(rcomma.base(), line.cend()) << std::endl; // LAST
```

注意，由于迭代器区间左闭右开的性质，用 `base()` 转换后迭代器指向下一个位置，如 `ABCD` 中若 `riter` 指向 `A`，则 `riter.base()` 指向 `B`。

# 泛型算法结构

不同算法对迭代器的要求不同，大致可以分成五种。

| 类别           | 要求                                 |
| -------------- | ------------------------------------ |
| 输入迭代器     | 只读不写，单遍扫描，只能递增         |
| 输出迭代器     | 只写不读，单遍扫描，只能递增         |
| 前向迭代器     | 可读写，多遍扫描，只能递增           |
| 双向迭代器     | 可读写，多遍扫描，可递增递减         |
| 随机访问迭代器 | 可读写，多遍扫描，支持所有迭代器操作 |

## 五类迭代器

高级的迭代器可以用在低级迭代器需求的算法上，但是不能反过来。

- 输入迭代器：`std::istream_iterator`、算法 `std::find()` 和 `std::accumulate()`
  - 比较（`==`、`!=`）
  - 前置和后置的递增（`++`）
  - 解引用（`*`），且只出现在赋值运算符的右侧
  - 箭头（`->`）
- 输出迭代器 `std::ostream_iterator`、算法 `std::copy()`
  - 前置和后置的递增（`++`）
  - 解引用（`*`），且只出现在赋值运算符的左侧
- 前向迭代器：`std::forward_list` 的迭代器，算法 `std::replace()`
  - 输入和输出
- 双向迭代器：除 `std::forward_list` 以外的容器，算法 `std::reverse()`
  - 前置迭代器
  - 前置和后置的递减（`--`）
- 随机访问迭代器：如 `std::array`、`std::vector`、`std::deque`、`std::string`、算法 `std::sort`
  - 支持所有操作
  - 可以在常量时间内访问任意元素

## 算法形参模式

算法形参一般是四种类型：

- `alg(beg, end, [args])`
- `alg(beg, end, dest, [args])`（接受写入位置的迭代器，默认可以已知写入元素）
- `alg(beg, end, beg2, [args])`（接受第二个序列，要求第二个序列至少和第一个一样长）
- `alg(beg, end, beg2, end2, [args])`（接受第二个序列）

## 命名规范

- 接受谓词：`unique(beg, end)`、`unique(beg, end, pred)`
- `_if`：（将变量换成谓词）`find(beg, end, val)`、`find(beg, end, pred)`
- `_copy`：（将结果拷贝到新序列上）`reverse(beg, end)`、`reverse(beg, end, beg2)`
- `_copy_if`：同上组合

# 特定容器算法

`std::list` 和 `std::forward_list` 由于结构不同，普通的算法会比较慢，因此有特殊版本的算法。

| 操作                                       | 作用                                                                    |
| ------------------------------------------ | ----------------------------------------------------------------------- |
| `lst.merge(lst2)`, `lst.merge(lst2, comp)` | 合并两个有序列表，其中 `list2` 会被清空。默认用 `<`，可以用 `comp` 替代 |
| `lst.remove(val)`, `lst.remove(pred)`      | 用 `erase()` 删除和给定值相等或满足谓词的元素                           |
| `lst.reverse()`                            | 反转列表                                                                |
| `lst.sort()`, `lst.sort(comp)`             | 用 `<` 或 `comp` 排序                                                   |
| `lst.unique()`, `lst.unique(cmp)`          | 用 `<` 或 `comp` 删除连续值                                             |

注意链表的特殊版本会对输入序列（比如 lst2）造成影响。

## `splice()`

除此之外，`splice()` 算法是 list/forward_list 特有的。（`lst.splice(args)`, `flist.splice_after(args)`)

对于 `std::list`（`p` 是 `lst` 的迭代器）：

| 参数              | 作用                                                                                   |
| ----------------- | -------------------------------------------------------------------------------------- |
| `(p, lst2)`       | 函数将 `lst2` 所有元素移动到 `p` 之前并清空 `lst2`；`lst` 和 `lst2` 不能相同           |
| `(p, lst2, p2)`   | `p2` 是 `lst2` 迭代器。函数将 `p2` 指向的元素移动到 `lst` 中。`lst` 和 `lst2` 可以相同 |
| `(p, lst2, b, e)` | 迭代器区间属于 `lst2`，函数将其移动到 `lst2`；`lst` 和 `lst2` 可以相同                 |

对于 `std::forward_list`（`p` 是 `lst` 迭代器和首前迭代器）：

| 参数              | 作用                                                                                     |
| ----------------- | ---------------------------------------------------------------------------------------- |
| `(p, lst2)`       | 函数将 `lst2` 所有元素移动到 `p` 之后并清空 `lst2`；`flst` 和 `lst2` 不能相同            |
| `(p, lst2, p2)`   | `p2` 是 `lst2` 迭代器。函数将 `p2` 之后的元素移动到 `flst` 中。`flst` 和 `lst2` 可以相同 |
| `(p, lst2, b, e)` | 迭代器区间属于 `lst2`，函数将其移动到 `lst2`；`flst` 和 `lst2` 可以相同                  |
