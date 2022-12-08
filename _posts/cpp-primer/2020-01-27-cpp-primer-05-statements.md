---
layout: "post"
title: "「C++ Primer」 05 Statements"
subtitle: "语句"
author: "roife"
date: 2020-01-27

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# `if`

`if-else` 语句在嵌套时要多使用花括号，避免歧义。一般 `else` 会与离他最近的 `if` 语句相匹配。

# `switch`

`switch` 语句只能对整型使用，`case` 标签必须是常量表达式，且任何两个 `case` 标签不能相同。

不能遗漏 `break` 语句，且尽量写 `default` 语句。

在 `switch` 语句中，定义的变量可以被后续的 `case` 语句所继承，但是要求被定义的变量不能进行初始化（可以定义在大括号里）。

``` cpp
switch(i) {
    case 0:
        int ival; // 合法
        int jval = 1; // 非法，不能初始化
        std::string s; // 非法，已经被隐式初始化
        break;
    case 1:
        ival = 1;
        std::cout << ival << std::endl;
}
```

> 总结：`switch` 语句一般只用于 `enum` 类型。

# 循环

使用 `range for` 的对象必须是用花括号的初始化列表、数组、有迭代器的对象等。

``` cpp
std::vector<int> v = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};

for (auto &i: v) {
    i *= 2;
}

for (auto beg = v.begin(), end = v.end(); beg != end; ++beg) {
    *beg *= 2;
} // 等价
```

由此可见，由于 `v.end()` 在循环初始就已经确定，因此不可以用 `v.push_back()` 再添加数据。

`do-while` 循环不允许在条件部分定义变量。

# 跳转语句

`goto` 的语法是 `goto label;`，`label` 的定义是 `label: stmt;`

标签可以和变量等标识符用同一个名字，但是 `goto` 语句和 `label` 必须在同一个函数内。

和 `switch` 语句一样，`goto` 能跳过变量的定义，并且在后续过程中可以使用，但是不能跳过变量的初始化。

``` cpp
goto end;
int x; // 合法
int y = 1; // 非法
end: x = 1; // 合法
```

如果 `goto` 使用时遇到了一个已经执行的定义语句，那么这个变量会被重新定义并初始化。

``` cpp
begin: int ival = f();
if (ival <= 0) goto begin;
```

# 异常处理

## `throw`

`throw` 后跟的表达式类型即异常类型，如 `throw std::runtime_error("xxx");`，`std::runtime_error` 定义在 `stdexcept` 头文件中。

## `try`

``` cpp
try {
    int a, b;
    std::cin >> a >> b;
    if (!b) throw std::runtim_error("Divisor could't be 0");
} catch (std::runtime_error &err) {
    std::cout << err.what()
              << "Try again";
}
```

注意在 `try` 中定义的变量无法在 `catch` 中访问。

在使用 `try` 语句时可能会发生嵌套，如果 `throw` 抛出的异常无法在对应的 `catch` 中找到，则回到上一层的 `try`。如果还是不能找到，则终止当前函数，继续往上找 `catch`。若始终无法找到，则会转到标准库函数 `std::terminate()` 上。这个函数由系统定义，一般代表程序的非正常退出。

抛出异常可能使得一部分计算被中断，可能导致对象无效或资源没有被正常释放。因此在异常中需要编写清理这些问题的代码。

## 标准异常

有四个头文件可以用来处理异常：

- `exception`：定义了异常类 `std::exception`，只报告异常的发生，不能提供额外的信息
- `stdexcept`：定义了常用的异常类
- `new`：定义了 `bad_alloc` 异常类型
- `type_info`：定义了 `bad_cast` 类型

| 类                      | 作用                   |
| ----------------------- | ---------------------- |
| `exception`             | 应用最广泛             |
| `std::runtime_error`    | 运行时错误             |
| `std::range_error`      | 结果超出值域范围       |
| `std::overflow_error`   | 上溢                   |
| `std::underflow_error`  | 下溢                   |
| `std::logic_error`      | 逻辑错误               |
| `std::domain_error`     | 参数对应的结果不存在   |
| `std::invalid_argument` | 无效参数               |
| `std::length_error`     | 对象长度超出范围       |
| `std::out_of_range`     | 使用了超出有效范围的值 |

这些类中定义了异常对象的创建，复制，赋值的几种运算。

`std::exception`、`std::bad_alloc`、`std::bad_cast` 只能用默认初始化，不能提供初始值；其它异常类型则必须用 `std::string` 或字符串初始化提供错误信息。

异常类只定义了 `what()` 函数，返回是 `const char*` 类型，若不提供初始值，则由编译器决定返回值，提供和异常相关的文本信息。
