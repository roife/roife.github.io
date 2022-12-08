---
layout: "post"
title: "「C++ Primer」 17 Specialized Library Facilities"
subtitle: "tuple / bitset / regex / random / IO"
author: "roife"
date: 2020-08-13

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# `std::tuple`

`tuple` 定义在头文件 `tuple` 中。

| 操作                                             | 作用                                                                                             |
| ------------------------------------------------ | ------------------------------------------------------------------------------------------------ |
| `std::tuple<T1, T2, ..., Tn>`                    | 初始化含 `n` 个对象的 `tuple`，类型分别为 `T1, T2, ..., Tn`                                      |
| `std::tuple<T1, T2, ..., Tn> t(v1, v2, ..., vn)` | 用 `v1, v2, ..., vn` 个成员初始化 `tuple`，类型分别为 `T1...Tn`                                  |
| `std::make_tuple(v1, v2, ..., vn)`               | 用给定初始值初始化 `tuple`                                                                       |
| `t1 == t2`, `t1 != t2`, `t1 op t2`               | 比较两个 `tuple`（字典序，短路）                                                                 |
| `std::get<i>(t)`                                 | 获取第 `i` 个元素，左右值类型与 `t` 相同                                                         |
| `std::tuple_size<tupleType>::value`              | 类模板，有一个名为 `value` 的 `public constexpr static` 成员，类型为 `size_t`，表示 `tuple` 大小 |
| `tuple_element<i, tupleType>::type`              | 类模板，有一个名为 `type` 的 `public` 成员，表示给定 `tuple` 类型第 `i` 个成员的类型             |

## 初始化和基本运算

### 初始化

可以用构造函数或 `std::make_tuple()` 来初始化。

``` cpp
std::tuple<std::string, std::vector<double>, int, std::list<int>>
someVal("Constants", {3.14, 2.718}, 42, {0, 1, 2, 3, 4, 5});

auto item = std::make_tuple("0-999-78345-X", 3, 20.00);
```

### 访问成员

从 `0` 开始计数。

``` cpp
auto book = std::get<0>(item);
std::get<0>(item) *= 2;
```

也可以通过类模板来获取 `tuple` 信息。

``` cpp
typedef decltype(item) trans;
size_t sz = std::tuple_size<trans>::value;
std::tuple_element<1, trans>::type cnt = get<1>(item);
```

### 比较运算

比较时要求两侧 `tuple` 元素数量相等，而且每一对对象的比较都必须合法。

``` cpp
std::tuple<std::string, std::string> duo("1", "2");
std::tuple<int, int> twoD(1, 2);
std::tuple<size_t, size_t, size_t> threeD(1, 2, 3);

bool b = (duo == twoD); // 非法
bool b2 = (twoD == threeD); // 非法
```

## 用 `std::tuple` 返回多个值

把 tuple 作为返回值。

``` cpp
std::tuple<int, int>
findBook(std::string) {
    // ...
}
```

# `std::bitset`

`bitset` 定义在头文件 `bitset` 中。

## 定义和初始化

定义 `std::bitset` 时必须声明包含多少二进制位，且大小为常量表达式。（需要编译期推断出来）

| 语句                                      | 作用                                                                                                           |
| ----------------------------------------- | -------------------------------------------------------------------------------------------------------------- |
| `std::bitset<n> b`                        | 有 `n` 位，每一位都是 `0`，`constexpr` 函数                                                                    |
| `std::bitset<n> b(ull)`                   | 拷贝自 `unsigned long long` 的低 `n` 位，不足位补 `0`，`constexpr` 函数                                        |
| `std::bitset<n> b(s, pos, m, zero, one)`  | 拷贝自 `std::string` 的 `s`，`b` 拷贝自 `s` 的 `pos` 起 `m` 个字符，`s` 中只能包含 `zero` 或 `one`，对应 `0/1` |
| `std::bitset<n> b(cp, pos, m, zero, one)` | 同上，其中 `cp` 为字符数组                                                                                     |

其中后两个函数的字符串如果不符合要求，会抛出 `std::invalid_argument` 异常。

- 对于 `std::string`
  - `pos` 默认为 `0`
  - `m` 默认为 `std::string::npos`
  - `zero` 默认为 `'0'`
  - `one` 默认为 `'1'`
- 对于 `cp`
  - 如果没有提供 `m`，则要求 `cp` 以 `\0` 结尾
  - 如果提供了 `m`，则要求 `cp` 至少有 `m` 个字符

### `unsigned` 初始化

不足位补 `0`，多余位丢弃。

``` cpp
std::bitset<13> bitvec1(0xbeef);
```

### 字符串初始化

子串右侧为最低位。

``` cpp
std::bitset<32> bitvec4("1100");
```

## `std::bitset` 操作

| 操作                     | 作用                                                         |
| ------------------------ | ------------------------------------------------------------ |
| `b.any()`                | 是否有 `1`                                                   |
| `b.all()`                | 是否都是 `1`                                                 |
| `b.none()`               | 是否都是 `0`                                                 |
| `b.count`                | 多少 `1`                                                     |
| `b.size()`                | 有几位，`constexpr` 函数                                     |
| `b.test(pos)`            | 第 `pos` 位是否为 `1`                                        |
| `b.set(pos, v)`          | 将第 `pos` 位设置为 `bool` 的 `v`, `v` 默认为 `1`            |
| `b.set()`                | 把 `b` 全部变成 `1`                                          |
| `b.reset(pos)`           | 将第 `pos` 位设置为 `0`                                      |
| `b.reset()`              | 将 `b` 全部设置为 `0`                                        |
| `b.flip(pos)`            | 翻转第 `pos` 位                                              |
| `b.flip()`               | 翻转所有位                                                   |
| `b[pos]`                 | 访问第 `pos` 位，如果 `b` 为 `const` 则返回一个 `bool` 型    |
| `b.to_ulong()`           | 转换为 `unsigned long`，如果放不下抛错 `std::overflow_error` |
| `b.to_ullong()`          | 同上，转换为 `unsigned long long`                            |
| `b.to_string(zero, one)` | 返回 `std::string`, `zero` 默认为 `'0'`, `one` 默认 `'1'`    |
| `os << b`, `is >> b`     | 输出读入（`0/1`）直到非 `0/1`                                |

需要注意的是下标运算符 `[]` 对 `const` 类型进行了重载，对于非 `const` 可以用下标运算符进行操作。

``` cpp
bitvec[0] = 0;
```

# `std::regex`

正则表达式库定义在头文件 `regex` 中。

| 名称                   | 作用                                              |
| ---------------------- | ------------------------------------------------- |
| `std::regex`           | 正则表达式类                                      |
| `std::regex_match()`   | 检查是否匹配整个表达式，返回 `bool`               |
| `std::regex_search()`  | 寻找是否有子串匹配，返回 `bool`                   |
| `std::regex_replace()` | 替换匹配                                          |
| `std::sregex_iterator` | 迭代器适配器，用 `std::regex_search` 遍历所有匹配 |
| `std::smatch`          | 容器类，保存结果                                  |
| `std::ssub_match`      | 在 `std::string` 中匹配的结果                     |

正则表达式函数的参数为 `(seq, m, r, mft)` 或 `(seq, r, mft)`。

- `seq`：字符序列，可以是 `std::string`，字符数组或者表示范围的一对迭代器
- `m`：可省略，是一个 `std::smatch` 对象，用来保存匹配的结果和细节
- `r`：正则表达式函数
- `mft`：类型为 `std::regex_constants::match_flag_type`，可选参数，会影响匹配过程

## 正则表达式

`std::regex` 默认使用的是 ECMAScript。

``` cpp
std::string pattern("[^c]ei"); // 查找不在 c 后面的字符串 ei
pattern = "[[:alpha:]]*" + pattern + "[[:alpha:]]*"; // 前后都有字母

std::regex r(pattern); // 构造 regex 对象
std::smatch results; // 保存结果
std::string test_str = "receipt freind theif receive";

if(std::regex_search(test_str, results, r)) {
    std::cout << results.str() << std::endl; // 输出匹配的单词
}
```

### 正则表达式选项

| 选项                  | 作用                                        |
| --------------------- | ------------------------------------------- |
| `std::regex r(re)`    | 其中 `re` 为正则表达式                      |
| `std::regex r(re, f)` | 同上，`f` 用来指定选项，默认为 `ECMAScript` |
| `r1 = re`             | 其中 `re` 是正则表达式                      |
| `r1.assign(re, f)`    | 等同于赋值，同上                            |
| `r.mark_count()`      | 其中 `r` 中子表达式的数量                   |
| `r.flags()`           | 返回 `r` 的标志集                           |

构造函数和赋值操作可能会抛出 `std::regex_error` 错误。

正则表达式 `re` 可以是以下几种：

- `std::string`
- 表示字符范围的迭代器对
- 字符数组
- 花括号组成的字符列表
- 字符指针和一个计数器

标准 `f` 可以是以下几种（定义在 `std::regex` 或
`std::regex::constants::syntax_option_type` 中）:

- `icase`：忽略大小写
- `nosubs`：不保存匹配的字符串
- `optimize`：执行速度优先于构造速度
- `ECMAScript`：使用 ECMAScript-262 的语法
- `basic`：使用 POSIX 基本语法
- `extended`：使用 POSIX 扩展语法
- `awk`：使用 POSIX awk 的语法
- `grep`：使用 POSIX grep 的语法
- `egrep`：使用 POSIX egrep 的语法

同样也是用 `std::regex::icase | std::regex::ECMAScript` 这样的语法。

``` cpp
std::regex("[[:alnum:]]+\\.(cpp|cxx|cc)$", std::regex::incase); // 忽略大小写
std::smatch results;
std::string filename;
while (std::cin >> filename) {
    if (std::regex_search(filename, results, r)) {
        std::cout << results.str() << endl;
    }
}
```

### 正则表达式编译错误

正则表达式的编译发生在运行时，即初始化或被赋予新值时编译（因此要谨慎创建，特别注意循环等地方的开销）。

若编译错误则会抛出 `std::regex_error` 异常，错误类型定义在 `std::regex` 和 `std::regex::regex_constants::error_type` 中。

| 错误类型           | 含义                                               |
| ------------------ | -------------------------------------------------- |
| `error_collate`    | 无效的元素校对请求                                 |
| `error_ctype`      | 无效的字符类                                       |
| `error_escape`     | 无效的转义字符或尾置转义                           |
| `error_backref`    | 无效的向后引用                                     |
| `error_brack`      | `[]` 不匹配                                        |
| `error_paren`      | `()` 不匹配                                        |
| `error_brace`      | `{}` 不匹配                                        |
| `error_badbrace`   | `{}` 中的范围无效                                  |
| `error_range`      | 无效的字符范围（如 `[z-a]`）                        |
| `error_space`      | 内存不足                                           |
| `error_badrepeat`  | 重复字符（`*`、`?`、`+`、`{`）之前没有有效地表达式 |
| `error_complexity` | 匹配过于复杂                                       |
| `error_stack`      | 栈空间不足                                         |

错误类型编号依次从 `0` 开始。

### 输入类型

| 序列类型       | 类                                                                         |
| -------------- | -------------------------------------------------------------------------- |
| `std::string`  | `std::regex`、`std::smatch`、`std::ssub_match`、`std::sregex_iterator`     |
| 字符数组       | `std::regex`、`std::cmatch`、`std::csub_match`、`std::cregex_iterator`     |
| `std::wstring` | `std::wregex`、`std::wsmatch`、`std::wssub_match`、`std::wsregex_iterator` |
| 宽字符数组     | `std::wregex`、`std::wcmatch`、`std::wcsub_match`、`std::wcregex_iterator` |

## 迭代器

使用迭代器可以获取所有类型的匹配。

| 迭代器操作                         | 作用                                                                 |
| ---------------------------------- | -------------------------------------------------------------------- |
| `std::sregex_iterator it(b, e, r)` | 利用 `r` 在 `b` 和 `e` 之间遍历，定位到第一个匹配的位置              |
| `std::sregex_iterator end`         | 尾后迭代器                                                           |
| `*it`, `it->`                      | 返回最近一次搜索的 `std::smatch` 对象或指向 `std::smatch` 对象的指针 |
| `++it`, `it++`                     | 从当前匹配位置开始调用 `std::regex_search()`（查找下一个）           |
| `it1 == it2`, `it1 != it2`         | 相等当且仅当都是尾后迭代器，或基于相同的 `std::regex` 和输入序列     |

``` cpp
for (std::sregex_iterator it(file.begin(), file.end(), r), endit;
    it != end_it; ++it) {
    std::cout << it->str() << std::endl;
}
```

## 匹配数据

| `std::smatch` 操作       | 作用                                                                             |
| ------------------------ | -------------------------------------------------------------------------------- |
| `m.ready()`              | 是否已经通过 `std::regex_search()` 和 `std::regex_match` 设置了 `m`（即是否可用）|
| `m.size()`               | 匹配失败返回 `0`，否则返回最近一次匹配中子表达式的数量                           |
| `m.empty()`              | `m.size()` 是否为 `0`                                                            |
| `m.prefix()`             | 一个 `std::ssub_match` 对象，表示当前匹配之前的序列                              |
| `m.suffix()`             | 一个 `std::ssub_match` 对象，表示当前匹配之后的部分                              |
| `m.length(n)`            | 第 `n` 个匹配子表达式的大小                                                      |
| `m.position(n)`          | 第 `n` 个子表达式据序列开始的位置                                                |
| `m.str(n)`               | 第 `n` 个子表达式匹配的字符串                                                    |
| `m[n]`                   | 对应第 `n` 个子表达式的 `std::ssub_match` 对象                                   |
| `m.begin()`, `m.end()`   | 表示 `m` 中元素范围的迭代器                                                      |
| `m.cbegin()`, `m.cend()` |                                                                                  |

如获取匹配位置的上下文：

``` cpp
for (std::sregex_iterator it(file.begin(), file.end(), r), end_it;
    it != end_it; ++it) {
    auto pos = it -> prefix().length();
    pos = pos > 40? pos - 40 : 0; // 最多获取 40 个字符

    std::cout << it->prefix.str().substr(pos) <<
        "\n\t\t>>> " << it->str() << " <<<\n" <<
        it->suffix().str().substr(0, 40) << std::endl;
}

// 输出：
// hey read or write according to the type
// >>> being <<<
// handled. The input operators ignore whi
```

## 子表达式

子表达式是原表达式中用括号包围的一部分，如 `"([[:alnum:]]+)\\.(cpp|cxx|cc)$"` 的两个子表达式为 `[[:alnum:]]` 和 `cpp|cxx|cc`。

第 `0` 个子表达式是整个串。

| 子匹配操作                  | 作用                                                       |
| --------------------------- | ---------------------------------------------------------- |
| `m[i].matched`              | `public bool` 成员，表示这个 `std::ssub_match` 是否匹配    |
| `m[i].first`, `m[i].second` | `public` 成员，表示匹配序列的首尾迭代器（如果不匹配则相等）|
| `m[i].length()`             | 匹配序列的长度                                             |
| `m[i].str()`                | 匹配序列的 `std::string`（不匹配则为空）                   |
| `s = ssub`                  | 等价于 `s = ssub.str()`                                    |

如匹配美国电话号码：

``` cpp
bool valid(const std::smatch& m) {
    if(m[1].matched) {
        return m[3].matched && (m[4].matched == 0 || m[4].str() == " ");
    } else {
        return !m[3].matched && (m[4].str() == m[6].str());
    }
}

std::string phone_pattern = "(\\()?(\\d{3})(\\))?([-. ])?(\\d{3})([-. ]?)(\\d{4})";
std::regex r(phone_pattern);
std::smatch m;
std::string s;

while(std::getline(std::cin, s)) {
    for (std::sregex_iterator it(s.begin(), s.end(), r), end_it;
        it != end_it; ++it) {
        if(valid(*it)) {
            std::cout << "valid: " << it->str() << std::endl;
        } else {
            std::cout << "not valid: " << it->str() << str::endl;
        }
    }
}
```

## `std::regex_replace()`

| 替换操作                                          | 作用                                                                                                                     |
| ------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------ |
| `m.format(dest, fmt, mft)`                        | 用 `fmt` 格式化输出。`mft` 表示标志，默认为 `std::regex_constants::format_default`.                                      |
| `m.format(fmt, mft)`                              | 同上                                                                                                                     |
| `std::regex_replace(dest, beg, end, r, fmt, mft)` | `beg`，`end` 为迭代器范围，用 `r` 遍历 `seq` 并用 `fmt` 和 `mft` 生成输出，`mft` 默认为 `regex_constants::match_default` |
| `std::regex_replace(seq, r, fmt, mft)`            | 同上，`seq` 为 `std::string` 或指向字符数组的指针                                                                        |

- 第一个版本中的 `dest` 为迭代器，表示写入的位置
- 第二个版本返回 `std::string`
- `mft` 可选
- `fmt` 可以是 `std::string` 或字符数组（如 `"$2.$5.$7"` 表示使用第 `2`、`5`、`7` 个参数）

### 格式标志

定义在 `std::regex_constants::match_flag_type` 中。

| 匹配标志            | 作用                                       |
| ------------------- | ------------------------------------------ |
| `match_default`     | 等价于 `format_default`                    |
| `match_not_bol`     | 不将首字符作为行首处理                     |
| `match_not_eol`     | 不将尾字符作为行尾处理                     |
| `match_not_bow`     | 不将首字符作为单词首处理                   |
| `match_not_eow`     | 不将尾字符作为单词尾处理                   |
| `match_any`         | 如果存在多于一个匹配，则可返回任意一个匹配 |
| `match_not_null`    | 不匹配任何空序列                           |
| `match_continuous`  | 匹配必须从输入的首字符开始                 |
| `match_prev_avail`  | 输入序列包含第一个匹配之前的内容           |
| `format_default`    | 用 ECMAScript 规则替换字符串               |
| `format_sed`        | 用 POSIX `sed` 规则替换字符串              |
| `format_no_copy`    | 不输出输入序列中未匹配的部分               |
| `format_first_only` | 只替换子表达式的第一次出现                 |

``` cpp
std::string fmt2 = "$2.$5.$7 ";
std::cout << std::regex_replace(s, r, fmt2, std::regex_constants::format_no_copy) << std::endl;
```

## Raw String Literal

Raw String Literal 格式为 `R"delim(...)delim"`，其中 `delim` 不超过 `16` 个字符，如：

``` cpp
std::string s0 = R"(\\)"; // 结果为 \\
std::string s1 = R"_LINE_("(1+2) == (2+1)")_LINE_"; // 结果为 "(1+2) == (2+1)"
```

在正则表达式中使用十分方便。

``` cpp
std::string pattern = R"R(('(?:[^\\']|\\.)*'|"(?:[^\\"]|\\.)*")|)R";
```

# 随机数

随机数相关函数定义在头文件 `random` 中，包含**随机数引擎类**和**随机数分布类**。

- 随机数引擎：生成随机的 `unsigned` 整数序列
- 随机数分布：使用引擎返回服从特定概率分布的随机数

## 随机数引擎

随机数引擎定义了 `()` 运算符返回随机数。

``` cpp
std::default_random_engine e;

for(size_t i = 0; i < 10; ++i) {
    std::cout << e() << ' ';
}
```

随机数库定义了多种引擎，其性能和随机性都不同，其中一种最常用的会被用作 `default_random_engine`。

随机数引擎生成的数字在 `e.min()` 和 `e.max()` 之间。

| 操作                       | 作用                           |
| -------------------------- | ------------------------------ |
| `std::Engine e`            | 默认构造函数，使用默认的种子   |
| `std::Engine e(s)`         | 使用整数 `s` 作种子            |
| `e.seed(s)`                | 使用种子 `s` 重置引擎          |
| `std::Engine::result_type` | 引擎生成的 `unsigned` 整数类型 |
| `e.min()`, `e.max()`       | 引擎可生成的最大最小值         |
| `e.discard(u)`             | 将引擎推进 `u` 步              |

## 随机数分布

一般随机数引擎生成的数字为原始随机数，需要随机数分布保证数字在需求范围内。

``` cpp
std::uniform_int_distribution<unsigned> u(0, 9); // 随机数分布，生成 0~9 之间的数字
std::default_random_engine e;

for (size_t i = 0; i < 10; ++i) {
    std::cout << u(e) << ' '; // 注意是 u(e) 而不是 u(e())，即传递引擎而不是数字
}
```

## 在函数中生成随机数

一个给定的随机数引擎会一直生成相同的随机数，因此在函数中使用时要用 `static` 修饰，保证每次调用函数生成的随机序列不同。

``` cpp
std::vector<unsigned>
good_randVec() {
    static std::default_random_engine e;
    static std::uniform_int_distribution u(0, 9);
    std::vector<unsigned> ret;

    for (size_t i = 0; i < 10; ++i) {
        ret.push_back(u(e));
    }

    return ret;
}
```

## 随机数种子

相同的随机数种子会生成相同的随机数序列，因此可以用 `ctime` 库中的系统时间函数。

``` cpp
std::default_random_engine e1(time(0)); // 注意这种方法只适合生成种子间隔至少为秒级别的情况
```

## 其它随机数

### 随机实数

使用 `std::uniform_real_engine`。

``` cpp
std::default_random_engine e;
std::uniform_real_distribution<double> (0, 1);

for (size_t i = 0; i < 10; ++i) {
    std::cout << u(e) << ' ';
}
```

同样 `std::uniform_real_engine` 也有类似的函数。同时支持用 `d.reset()` 来重建 `d` 的状态，使随后生成的值和之前生成的无关。

### 默认模板类型

整数随机数默认为 `int`，浮点数随机数默认为 `double`。

``` cpp
std::uniform_real_distribution<> u(0, 1); // double 类型
```

### 非均匀分布的随机数

如正态分布生成以 `4` 为中心，标准差为 `1.5` 的随机数。

``` cpp
std::default_random_engine e;
std::normal_distribution<> n(4, 1.5);
std::vector<unsigned> vals(9);

for (size_t i = 0; i != 200; ++i) {
    unsigned v = lround(n(e)); // 四舍五入
    if (v < vals.size()) ++vals[v];
}
```

### `std::bernoulli_distribution`

`std::bernoulli_distribution` 是一个类，而非模板，默认以 `0.5` 的概率返回 `true` 或 `false`。

``` cpp
std::default_random_engine e;
std::bernoulli_distribution b;
std::cout << b(e);
```

也可以指定 `true` 的概率。

``` cpp
std::bernoulli_distribution b(.55);
```

# IO 库再探

## 格式控制

操作符对于格式的改变是持久的，因此最好在使用后尽快将流恢复到默认状态。

`setprecision` 和其它接受参数的操作符定义在头文件 `iomanip`。

### 控制 `bool` 的输出

输出 `bool` 值时，`true` 默认输出 `1`，`false` 默认输出 `0`。

- `std::boolalpha`
  : 用 `true` 或 `false` 来替代 `0/1`
- `std::noboolalpha`
  : 恢复 `std::boolalpha`

``` cpp
std::cout << true << " " <<
    std::boolalpha << true << " " <<
    std::noboolalpha << std::endl;
// 输出 1 true
```

### 整数进制

- `std::dec`：输出十进制
- `std::oct`：输出八进制
- `std::hex`：输出十六进制
- `std::setbase(n)`：设定输出的进制

注意操作符的作用是持久的，且只影响整数（不影响浮点数）。

``` cpp
std::cout << 20 << " " <<
    std::oct << 20 << " " <<
    std::hex << 20 << " " <<
    std::dec << 20 << std::endl;

// 输出 20 24 14 20
```

- `std::showbase`：显示进制（前导 `0x` 表示十六进制，前导 `0` 表示八进制，否则为十进制）
- `std::noshowbase`：恢复 `std::showcase`
- `std::uppercase`：默认十六进制用小写表示，改变之后可以用大写
- `std::nouppercase`：恢复 `std::uppercase`

### 补白

- `std::setw(n)`：指定下一个数字或字符串的最小空间
- `std::left`：左对齐
- `std::right`：右对齐
- `std::internal`：左对齐符号，右对齐值，中间用空格填满
- `std::setfill(c)`：用指定字符代替空白补白

``` cpp
int i = -16;
double d = 3.14159;
std::cout << "i: " << std::setw(12) << i << "next col" << '\n' <<
    "d: " << std::setw(12) << d << "next col" << '\n';

std::cout << std::left <<
    "i: " << std::setw(12) << i << "next col" << '\n' <<
    "d: " << std::setw(12) << d << "next col" << '\n' <<
    std::right;

std::cout << std::right <<
    "i: " << std::setw(12) << i << "next col" << '\n' <<
    "d: " << std::setw(12) << d << "next col" << '\n';

std::cout << std::internal <<
    "i: " << std::setw(12) << i << "next col" << '\n' <<
    "d: " << std::setw(12) << d << "next col" << '\n';

std::cout << std::setfill('#') <<
    "i: " << std::setw(12) << i << "next col" << '\n' <<
    "d: " << std::setw(12) << d << "next col" << '\n' <<
    std::setfill('#');
```

- `std::showpos`：对于非负数显示 `+`
- `std::noshowpos`：对于非负数不显示 `+`

### 输入格式控制

- `std::skipws`：跳过空白符（默认）
- `std::noskipws`：不跳过空白符

``` cpp
char ch;
std::cin >> std::noskipws;
while (std::cin >> ch) std::cout << ch;
std::cin >> std::skipws;
```

## 浮点数格式控制

浮点数格式内容包括：

- 精度（默认 `6` 位）
- 记数法，包括进制和科学计数法等（默认定点十进制，非常大的数字和非常小的数字用科学计数法）
- 对于无小数点的数字是否打印小数点（默认不打印）

### 精度

- `std::cout.precision(int)` 或 `std::cout.setprecision(int)`：设置精度
- `std::cout.precision()`：返回当前精度

``` cpp
std::cout << "Precision: " << std::cout.precision() <<
    ", Value: " << sqrt(2.0) << std::endl;
std::cout.precision(12);

std::cout << "Precision: " << std::cout.precision() <<
    ", Value: " << sqrt(2.0) << std::endl;

std::cout.setprecision(12);
std::cout << "Precision: " << std::cout.precision() <<
    ", Value: " << sqrt(2.0) << std::endl;

// 输出
// Precision: 6, Value: 1.41421
// Precision: 12, Value: 1.41421356237
// Precision: 3, Value: 1.41
```

### 记数法

- `std::scientific`：使用科学计数法
- `std::hexfloat`：使用十六进制
- `std::fixed`：使用十位定点
- `std::defaultfloat`：使用默认方式

对于十六进制和科学计数法，可以用 `std::uppercase` 使字母大写。

``` cpp
std::cout << "default format: " << 100 * sqrt(2.0) << '\n' <<
    "scientific: " << std::scientific << 100 * sqrt(2.0) << '\n' <<
    "fixed decimal: " << std::fixed << 100 * sqrt(2.0) << '\n' <<
    "use defaults: " << std::defaultfloat << 100 * sqrt(2.0);

// 输出
// default format: 141.421
// scientific: 1.414214e+002
// fixed decimal: 141.421356
// hexadecimal: 0x1.1ad7bcp+7
// use defaults: 141.421
```

### 小数点

- `std::showpoint`：定义小数点
- `std::noshowpoint`：不打印小数点

``` cpp
std::cout << 10.0 << std::endl; // 打印 10
std::cout << std::showpoint << 10.0 << // 打印 10.0000
    std::noshowpoint << std::endl;
```

## 未格式化的输入输出控制

即将流当成一个无解释的字符序列。

### 单字节操作

| 操作             | 作用                                          |
| ---------------- | --------------------------------------------- |
| `is.get(ch)`     | 读取下一个字节到 `ch`，返回 `is`              |
| `os.put(ch)`     | 输出 `ch` 到 `os`，返回 `os`                  |
| `is.get()`       | 将 `is` 的下一个字节作为数字返回              |
| `is.putback(ch)` | 将字节 `ch` 放回 `is`，返回 `is`              |
| `is.unget()`     | 将 `is` 向后移动一个字节，返回 `is`           |
| `is.peek()`      | 将下一个字节作为 `int` 返回，但是不从流中删除 |

由于是当作字节流，因此不会忽略空白字符。

### 将字节放回输入流

- `is.peek()`：返回输入流的下一个字符，但是不会删除字符
- `is.unget()`：使读入的字符回到流中
- `is.putback(c)`：将 `c` 放回输入流

`std::putback()` 和 `std::unget()` 不能连续使用，中间必须有其他的读入操作。

### 输入控制返回 `int`

输入控制返回 `int` 而非 `char`，因为会返回尾标记之类的特殊字符。

如定义在 `cstdio` 中的 `EOF` 可以用来检测是否读到文件尾。

``` cpp
int ch; // 注意不能是 char
while ((ch = std::cin.get()) != EOF) {
    std::cout.put(ch);
}
```

### 多字节操作

- `is.get(sink, size, delim)`：从 `is` 中读入字符存到字符数组 `sink` 中，最多读入 `size` 个字符，遇到 `delim` 或读入了 `size`个字符或遇到文件尾时停止。（不会读入 `delim`)
- `is.getline(sink, size, delim)`：同上，会读取 `delim` 并将其丢弃
- `is.read(sink, size)`：同上
- `os.write(source, size)`：将 `source` 的 `size` 个字符写入 `os`
- `is.ignore(size, delim)`：读入并忽略 `size` 个字符或遇到 `delim` 时停止，`size` 默认为 `1`, `delim` 默认为文件尾

无论哪个操作都不会保存 `delim`。

### 读入字符数量

- `is.gcount()`：上一个未格式化操作读入的字符数

如果使用了 `peek()`、`unget()`、`putback()`，那么 `gcount()` 返回 `0`

## 流随机访问

`std::istream` 与 `std::ostream` 不支持随机访问，运行时会出错。

`std::fstream` 与 `std::sstream` 指出随机访问。

### `ios.seek()` 与 `ios.tell()`

| 函数                  | 作用                                        |
| --------------------- | ------------------------------------------- |
| `is.tellg()`          | 返回**输入流**中标记当前的位置            |
| `is.seekg(pos)`       | `pos` 为流中的位置，重定位到给定的位置      |
| `is.seekg(off, from)` | 将标记定位到距 `from` 偏移值为 `off` 的位置 |
| `os.tellp()`          | 返回**输出流**中标记当前的位置            |
| `os.seekp(pos)`       | `pos` 为流中的位置，重定位到给定的位置      |
| `os.seekp(off, from)` | 将标记定位到距 `from` 偏移值为 `off` 的位置 |

`pos` 和 `from` 类型为 `std::ios::pos_type`，`off` 类型为 `std::ios::off_type`。

`seekp` 中的 `from` 可以是以下三个值：

- `std::ios:beg`：流开始的位置
- `std::ios:cur`：流当前的位置
- `std::ios:end`：流结束的位置

对 `std::ifstream` 使用 `tellp()` 或对 `std::ostringstream` 使用 `seekg()`都会导致错误。

### 只有一个标记

`std::fstream` 的读写控制的是同一个标记，`std::stringstream` 控制的是不同的标记。

对于 `std::fstream` 和 `std::stringstream` 等既能读又能写的流，在读写操作之间切换前必须用 `seek()` 重定位标记（即使是到当前位置）。

### `ios.tell()`

``` cpp
std::ostringstream writeStr;
std::ostringstream::pos_type mark = writeStr.tellp();

if(cancelEntry) {
    writeStr.seekp(mark);
}
```
