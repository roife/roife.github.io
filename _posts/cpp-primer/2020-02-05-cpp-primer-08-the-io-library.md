---
layout: "post"
title: "「C++ Primer」 08 The IO Library"
subtitle: "IO 库"
author: "roife"
date: 2020-02-05

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# IO 类

| 头文件                  | 类型                                        |
| ----------------------- | ------------------------------------------- |
| `iostream` 流           | `std::istream`, `std::wistream`             |
|                         | `std::ostream`, `std::wostream`             |
|                         | `std::iostream`, `std::wiostream`           |
| `fstream` 文件          | `std::ifstream`, `std::wifstream`           |
|                         | `std::ofstream`, `std::wofstream`           |
|                         | `std::fstream`, `std::wfstream`             |
| `sstream` `std::string` | `std::istringstream`, `std::wistringstream` |
|                         | `std::ostringstream`, `std::wostringstream` |
|                         | `std::stringstream`, `std::wstringstream`   |

`w` 开头的类型都是用来操控 `wchar_t` 的。

`ifstream` 和 `istringstream` 继承自 `istream`，类似还有其它继承关系。

## IO 对象不可拷贝赋值

函数的形参和返回值是 IO，只能用引用的形式，并且不能使用 `const`（会无法读写）。

``` cpp
std::ofstream out1, out2;
out1 = out2; // 非法
std::ofstream print(std::ofstream); // 函数定义非法
```

## 条件状态

可以用 `strm` 表示某种 `stream`（如 `istream`）。

| 函数/标志            | 条件状态                                   | 返回值               |
| -------------------- | ------------------------------------------ | -------------------- |
| `std::strm::iostate` | 条件状态的类型，都是 `constexpr`           |                      |
| `std::strm::badbit`  | 流已崩溃                                   |                      |
| `std::strm::failbit` | IO 操作失败                                |                      |
| `std::strm::eofbit`  | 文件结束                                   |                      |
| `std::strm::goodbit` | 流未出错，值为 `0`                         |                      |
| `s.eof()`            | `std::strm::eofbit`                        | `bool`               |
| `s.fail()`           | `std::strm::failbit` / `std::strm::badbit` | `bool`               |
| `s.bad()`            | `std::strm::badbit` 是否置位               | `bool`               |
| `s.good()`           | 是否有效                                   | `bool`               |
| `s.clear()`          | 清除所有错误，并将流设置为有效             | `void`               |
| `s.clear(flags)`     | 从 `flags` 复位                            | `void`               |
| `s.setstate(flags)`  | 设置为 `flags`                             | `void`               |
| `s.rdstate()`        | 返回条件状态                               | `std::strm::iostate` |

### `clear(flags)` 和 `setstate(flags)`

- `clear(flags)`：覆盖原始状态
- `setstate(flags)`：在原始状态上叠加新状态

``` cpp
std::cin.clear(std::istream::failbit | std::istream::badbit | std::stream::eofbit); // 结果为 7 = 4 + 2 + 1
std::cin.clear(std::istream::failbit); // 结果为 4
std::cin.setstate(std::istream::badbit | std::istream::eofbit); // 结果为 7 = 4 + 2 + 1

std::cin.clear((std::cin.rdstate() & ~std::cin.failbit) | ~std::cin.badbit); // 设置 failbit 为 0, badbit 为 1，位运算技巧
```

### `std::strm::iostate`

`iostate` 用二进制位来表示状态，一个流可以是多个状态的叠加：

- `badbit` 表示系统级错误，不可恢复
- `failbit` 表示读入错误（如把字符读入 int）、可以修正
- 读到文件结束时，`eofbit` 和 `failbit` 会被同时置位
- `badbit`、`eofbit`、`failbit` 任意一个为 `1` 都代表流的状态异常

只有流处于有效状态才可以使用，可以用条件判断流是否有效，如 `while (std::cin >> word)`（其实是检查 `!std::cin.fail()`）。

## 输出缓冲

流中的文本会被先保存在一个缓冲区中，缓冲机制可以减少程序和设备的操作，提高效率。

导致缓冲刷新的原因有以下几个：

- 程序结束
- 缓冲区满了
- 操作符如 `std::endl`
- 用 `std::unitbuf` 设置流的内部状态来清空缓冲区
- 两个流关联，对一个流进行读写，另一个流会刷新

注意：程序崩溃缓冲区不会刷新！因此调试程序时要确保缓冲区已刷新，否则将看不到任何输出。

### 刷新输出缓冲区的操作符

- `std::endl`：换行并刷新
- `std::flush`：仅刷新
- `std::ends`：输出空白字符并刷新

### `std::unitbuf` 与 `std::nounitbuf`

``` cpp
std::cout << std::unitbuf
```

`std::unitbuf` 会使流每次输出后都刷新，`std::nounitbuf` 则使流回到正常状态。

## 关联流

输入流和输出流关联时，对一个流操作会引起另一个流刷新，适合交互式程序使用。

用 `tie()` 函数可以将 `std::istream` 关联到 `std::ostream`，或者将一个 `std::ostream` 关联到另一个 `std::ostream`。

- `tie()` 无参数：返回关联的 `std::ostream` 的指针或 `nullptr`
- `tie(&os)` 有参数：参数为 `std::ostream` 的指针，将对象关联到这个 `std::ostream`，并返回用来关联的 `std::ostream` 的指针

``` cpp
std::cin.tie(&std::cout);

std::ostream *oldTie = std::cin.tie(&std::cerr); // oldTie == &std::cout

std::cin.tie(nullptr); // 取消关联
```

# 文件输入输出

`std::fstream` 也可以用 `std::cin`, `std::cout`, `std::getline`，并且特殊操作：

| 操作                          | 作用                                                                                      | 返回   |
| ----------------------------- | ----------------------------------------------------------------------------------------- | ------ |
| `std::fstream fstrm`          | 创建文件流                                                                                |        |
| `std::fstream fstrm(s)`       | 打开名为 `s` 的文件，`s` 为 `std::string` 或字符数组，`mode` 依赖于 `std::fstream` 的类型 |        |
| `std::fstream fstrm(s, mode)` | 指定一个 mode                                                                             |        |
| `fstrm.open(s)`               | 打开名为 `s` 的文件                                                                       | `void` |
| `fstrm.close()`               | 关闭绑定的文件                                                                            | `void` |
| `fstrm.is_open()`             | 返回文件是否成功打开且未关闭                                                              | `bool` |

其中构造函数都是 `explicit` 的。

## 文件流对象

所有 `std::istream&` / `std::ostream&` 的对象都可以替换为 `std::ifstream` / `std::ofstream`。

``` cpp
std::ifstream in(ifile);
std::ofstream out;
out.open(ifile + ".copy"); // 打开文件

if (out) {} // 检验是否打开成功
```

调用 `open()` 失败会使得 `failbit` 置位。

对一个已经打开的文件流使用 `open()` 也会使得 `failbit` 置位，想要关联到另外一个文件，要先 `close()`。

``` cpp
in.close();
in.open(ifile2);
```

文件流对象有自动的构造和析构函数，会在对象被销毁时自动关闭文件。

## 文件模式

| 模式                 | 含义                         |
| -------------------- | ---------------------------- |
| `std::fstrm::in`     | 读                           |
| `std::fstrm::out`    | 写                           |
| `std::fstrm::app`    | 每次写前定位到文件尾         |
| `std::fstrm::ate`    | 打开文件时立即定位到文件尾部 |
| `std::fstrm::trunc`  | 截断文件（清空原有内容）       |
| `std::fstrm::binary` | 以二进制形式进行 IO          |

文件模式设定也是用类似于位运算的操作。

文件模式的设置有以下几条限定：

- `std::fstrm::out` 只能设定 `std::ofstream`、`std::fstream`

- `std::fstrm::in` 只能设定 `std::ifstream`、`std::fstream`

- `std::fstrm::trunc` 必须和 `std::fstrm::out` 一起用

- 用了 `std::fstrm::app` 不加 `std::fstrm::out` 也能写文件

- 默认情况，即使不加 `std::fstrm::trunc`，`std::fstrm::out` 也会截断文件，可以附加 `std::fstrm::app` 或 `std::fstrm::in` 来避免

- `std::fstrm::ate` 和 `std::fstrm::binary` 可以任意使用

`std::istream` 默认用 `std::fstrm::in` 打开，`std::ostream` 默认用 `std::fstrm::out` 打开，`std::fstream` 默认用 `std::fstrm::in` + `std::fstrm::out` 打开。

`std::fstrm::ate` 与 `std::fstrm::in` 结合，可以用来计算文件大小。

``` cpp
// 以下三者等价，会清空原文件内容
std::ofstream out(ofile);
std::ofstream out(ofile, std::ofstream::out);
std::ofstream out(ofile, std::ofstream::out | std::ofstream::trunc);
// 以下两者等价，不会清空原文件内容
std::ofstream out(ofile, std::fstream::app);
std::ofstream out(ofile, std::fstream::out | std::fstream::app);
```

# 字符串流

可以向 `std::string` 中读写数据，拥有 `std::iostream` 的全部操作，除此之外还有操作：

| 操作                  | 作用                                     | 返回类型      |
| --------------------- | ---------------------------------------- | ------------- |
| `std::sstream strm`   | 创建字符串流                             |               |
| `std::stream strm(s)` | 同上，保存字符串 `s` 的拷贝（`explicit`） |               |
| `strm.str()`          | 返回 `strm` 保存的 `std::string` 拷贝    | `std::string` |
| `strm.str(s)`         | 将字符串 `s` 拷贝到 `strm` 中            | `void`        |

## `std::istringstream`

一般用于处理处理单词分割的问题。

``` cpp
struct PersonInfo {
    std::string name;
    std::vector<int> phones;
};

std::string line, word;
std::vector<PersonInfo> people;
while (getline(cin, line)) {
    PersonInfo info;
    std::istringstream record(line);
    record >> info.name;
    while (record >> word) info.phones.push_back(word);
    people.push_back(info);
}
```

注意：如果 `std::istringstream` 要重复使用，每次要用 `clear()` 清空。

`istringstream.str()` 调用完成后表达式会被析构，因此要慎用 `c_str()` 函数。

## `std::ostringstream`

一般用于逐步构造输出，最后一起打印。

``` cpp
for (const auto &entry: people) {
    std::ostringstream oss;
    for (const auto &num: entry.phones) {
        if (!valid(num)) oss << " " << num;
    }
    if (oss.str().size()) std::cout << entry.name << " " << oss.str() << std::endl;
}
```
