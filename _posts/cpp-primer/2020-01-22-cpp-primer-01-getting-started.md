---
layout: "post"
title: "「C++ Primer」 01 Getting Started"
subtitle: "开始"
author: "roife"
date: 2020-01-22

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 头文件

`#include "1.h"` 后可以调用在 `1.h` 中声明且在 `1.cc` 中定义的变量和函数。

一般用 `include` 展开的都是声明。

# 输入输出

`iostream` 库包含 `istream`（包括 `cin`）和 `ostream`（包括 `cout`、`cerr`、`clog`）两个基础类型。

- `<<`（`>>` 同理）

接受两个对象，左侧必须是 `std::ostream` 对象，右侧是打印的值，返回值是一个 `std::ostream` 对象。
`std::cout << "test" << std::endl` 等价于 `(std::cout << "test") << std::endl`。

- `std::endl`

结束当前行，并将内容刷新到设备上。

## 读入不定量的数据

``` cpp
while (std::cin >> value) // 当遇到 EOF 或者读入非数字时停止
```

# 注释

多行注释一般每行用 `*` 开头，不能嵌套。

``` cpp
/*
 * test
 * for
 * comments
 */

// test
```
