---
layout: "post"
title: "「C++ Primer」 03 Strings, Vectors, and Arrays"
subtitle: "字符串，向量和数组"
author: "roife"
date: 2020-01-24

tags: ["C++ Primer@读书笔记", "读书笔记@Tags", "C++@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# `using`

``` cpp
using std::cout;
using std::cin; // 每个名字都要单独声明，不能合并
using namespace std;
```

一般头文件不能包含 `using`。

# `std::string`

## 初始化

| 初始化                     | 作用                           |
| -------------------------- | ------------------------------ |
| `std::string s1`           | 默认初始化，空串               |
| `std::string s2(s1)`       | 拷贝                           |
| `std::string s2 = s1`      | 拷贝初始化                     |
| `std::string s3("value")`  | 用字面值初始化                 |
| `std::string s3 = "value"` | 同上                           |
| `std::string s4(n, 'c')`   | 初始化为 `n` 个 `'c'` 组成的串 |

通过等号初始化的方法被称为**拷贝初始化**，不用等号的方法称为**直接初始化**，二者一般没区别。

## `std::string` 对象的操作

| 操作                  | 作用                |
| --------------------- | ------------------- |
| `is>>s`, `os<<s`      | 输入输出            |
| `std::getline(is, s)` | 从 `is` 中读取一行  |
| `s.empty()`           | 判断是否为空        |
| `s.size()`            | 返回 `s` 中字符个数 |
| `s[i]`                | 返回第 `i` 个字符   |
| `s1+s2`, `s1+=s2`     | 连接                |
| `>=`, `!=` 等         | 比较                |

## 读入

读取 `std::string` 时读到空白字符就会停止，并丢弃空白字符。

如果希望保留空白字符应该使用 `std::getline`，可以用 `while (std::getline(std::cin, s))` 来读取多行。

`std::getline` 遇到换行符就会停止，读进来换行符并将其丢弃。

## `std::string::size_type`

`s.size()` 的返回类型是 `std::string::size_type`。

`std::string::size_type` 是一个无符号类型，可以表示任何 `std::string` 类型的大小，且机器无关。

当使用 `auto len = s.size()` 时要注意 `len` 是无符号的，所以要保证运算的过程中都是正数，特别要小心 `int` 参与运算。

初始化长度有关的变量时，也常使用 `decltype(s.size()) cnt = 0`。

## 字符串类型连接

使用 `+` 作为连接符时，需要运算符两侧至少有一个 `std::string` 类型。

``` cpp
std::string s1 = "a" + "b"; // 非法
std::string s2 = s1 + "a" + "b"; // 合法，左结合
std::string s3 = s2 + "," + "world"; // 合法
std::string s4 = "a" + "b" + s1; // 非法
```

## 处理字符：`cctype`

| 函数          | 作用                     |
| ------------- | ------------------------ |
| `isalnum(c)`  | 判断数字或字母           |
| `isalpha(c)`  | 判断字母                 |
| `iscnctrl(c)` | 判断控制字符             |
| `isdigit(c)`  | 判断数字                 |
| `isgraph(c)`  | 判断可打印且非空格       |
| `islower(c)`  | 判断小写字母             |
| `isprint(c)`  | 判断可视或是空格         |
| `ispunct(c)`  | 判断是标点符号           |
| `isspace(c)`  | 判断是空格（包括制表符等） |
| `isupper(c)`  | 判断大写字母             |
| `isxdigit(c)` | 判断是十六进制数字       |
| `tolower(c)`  | 转小写字母               |
| `toupper(c)`  | 转大写字母               |

> `cname` 的头文件中的名字属于 `std`。

## 遍历与访问

### 访问

要访问单个内容应使用下标运算符 `[]`，接受的参数是 `std::string::size_type`。

访问不存在的位置是非法的行为，因此在访问 `s[0]` 之前也要检查 `s.empty()`。

### 遍历

一般使用 **range for** 或者下标遍历。

``` cpp
for (auto c: str) {
    std::cout<< c << std::endl;
}
```

如果要通过循环变量来改变原字符串内容的话，则要用引用的形式。

``` cpp
for (auto &c: str) {
    c = toupper(c);
}
```

用下表遍历时应使用 `decltype` 声明循环变量

``` cpp
for (decltype(s.size()) index = 0;
     index != s.size() && !isspace(s[index]);
     ++index) {

    s[index] = toupper(s[index]);
}
```

> 用下标运算符访问前一定要检查下标的合法性！

# `std::vector`

## 初始化

| 初始化                          | 作用                           |
| ------------------------------- | ------------------------------ |
| `std::vector<T> v1`             | 空 vector                      |
| `std::vector<T> v2(v1)`         | `v2 = v1`                      |
| `std::vector<T> v2 = v1`        | 同上                           |
| `std::vector<T> v3(n, val)`     | `v3` 包含了 `n` 个 `val`       |
| `std::vector<T> v4(n)`          | `v4` 包含了 `n` 个初始化的对象 |
| `std::vector<T> v7{n, val}`     | 同 `v3`                        |
| `std::vector<T> v5{a, b, c}`    | 初始值                         |
| `std::vector<T> v6 = {a, b, c}` | 同上                           |

提供的是初始元素的列表时，必须用花括号，即**列表初始化**。注意区分 `std::vector<int> v(1)` 与 `std::vector<int> v{1}`。

使用圆括号初始化时，会对元素进行**值初始化**（内置类型被初始化为 `0`，类类型用默认构造函数）。

### 花括号与值初始化

一般用花括号时，都是把花括号内的元素当成初始值。但是当列表初始化提供的参数与模板类型不匹配时，会自动采用值初始化。

``` cpp
std::vector<int> v1(1, 2);             // 包含一个元素 2
std::vector<int> v2{1,2};              // 包含两个元素 1, 2
std::vector<std::string> v3{10};       // 有 10 个元素值初始化，因为参数和模板类型不匹配，所以采用值初始化。
std::vector<std::string> v4{10, "hi"}; // 有 10 个 "hi"
```

## 添加元素

``` cpp
v.push_back(val);
```

除非需要初始值，否则 `std::vector` 一般不需要在初始化时指定大小。

使用 `range for` 遍历 `std::vector` 时不应该添加元素。

## 其他 `std::vector` 的操作

| 操作            | 作用 |
| --------------- | ---- |
| `v.empty()`     |      |
| `v.size()`      |      |
| `v = {a, b, c}` | 赋值 |
| 比较运算        |      |
| `v[n]`          |      |

`v.size()` 和下标返回的也是 `std::vector<T>::size_type` 类型，如 `std::vector<int>::size_type`。

不能通过 `v[n]` 直接来给 `std::vector` 添加元素，因此访问前要保证下标存在。

## 迭代器

容器对象和 `std::string` 都支持迭代器。

``` cpp
auto b = v.begin(), e = v.end();
```

其中 `v.end()` 表示 `v` 的最后一个元素后的一个位置。因此可以用 `v.begin()!=v.end()` 来确保非空。

### 迭代器运算

| 运算           | 作用                   |
| -------------- | ---------------------- |
| `*iter`        | 迭代器指向元素的引用   |
| `iter->num`    | (\*iter).num           |
| `++iter`       | 指向下一个元素         |
| `--iter`       | 指向上一个元素         |
| `iter1==iter2` | 判断是否指向同一个元素 |
| `iter1!=iter2` |                        |

``` cpp
for (auto it = s.begin(); it != s.end() && !isspace(*it); ++it) {
    *it = toupper(*it);
}
```

一般这里使用 `!=`，因为并非所有库都定义了 `<` 等比较运算符。

使用迭代器时也不能使用 `push_back` 添加元素，否则迭代器可能会失效。（和 `std::vector` 的实现有关）

### 迭代器的类型

迭代器的类型为 `std::vector<T>::iterator`（如 `std::vector<int>::iterator`）。

同时有指向不可变元素的 `std::vector<T>::const_iterator` 类似于 `const int *`，只能读字符，而不能修改字符。当对象的定义为 `const std::vector<T>` 时，`v.begin()` 返回 const_iterator，否则返回 iterator。

可以使用 `v.cbegin()` 和 `v.cend()` 强制获取 `const_iterator`。

### 特殊迭代器运算

`std::string` 与 `std::vector` 中提供更多的迭代器运算。

| 运算             | 作用                                             |
| ---------------- | ------------------------------------------------ |
| `iter+n`         | 迭代器向后移动 `n` 位得到的新迭代器（类似于下标） |
| `iter-n`         | 迭代器向前移动 `n` 位得到的新迭代器              |
| `iter+=n`        | 迭代器向后移动 `n` 位                            |
| `iter-=n`        | 迭代器向前移动 `n` 位                            |
| `iter1-iter2`    | 两个迭代器间的距离                               |
| `<` 等比较运算符 | 比较两个迭代器                                   |

两个迭代器相减得到结果类型为 `std::vector<T>::difference_type`，是一个带符号整数。

``` cpp
// 一段用迭代器实现的二分查找：
auto beg = v.begin(), end = v.end();
auto mid = beg + (end - beg) / 2;

while (mid != end && *mid != sought) {
    if (sought < *mid) end = mid;
    else beg = mid + 1;
    mid = beg + (end - beg) / 2;
}
```

# 数组

## 初始化

数组定义时的维度必须是常量表达式，如 `const` 或者 `constexpr`（要确定占用空间）。

数组的类型不能用 auto 推导。

``` cpp
int cnt = 42;
constexpr unsigned sz = 42;

std::string bad[cnt]; // 非法
int arr[sz]; // 合法
```

### 列表初始化

列表初始化可以不声明数组的大小。

使用列表初始化时，如果只给出了前面部分的初始值，则后面部分会进行值初始化。

``` cpp
int a[]= {0, 1, 2};   // 包含三个元素
int b[5] = {0, 1, 2}; // 包含五个元素，{0, 1, 2, 0, 0}
int c[2] = {0, 1, 2}; // 非法
```

### 字符数组

字符数组可以用双引号初始化，并且会自动添加空字符 `\0`。

``` cpp
char a4[] = "C++";
const char a5[6] = "Daniel"; // 错误，无法存放 \0
```

### 数组的引用和指针

定义数组的引用和指针稍微复杂一些

``` cpp
int *ptrs[10]; // 对象为指针的数组
int &refs[10]; // 非法定义，不存在引用的数组

int (*Parray)[10] = &arr; // Parray 指向一个数组
int (&arrRef)[10] = arr; // arrRef 为 arr 的引用

int *(&arry)[10]; // arry 为一个引用，引用的对象为一个包含 10 个整型指针的数组
```

从内到外来理解，如 `int (*Parray)[10]` 首先看括号，确定个 `Parray` 是一个指针，然后确定是一个整型数组的指针。

## 访问与遍历

访问数组下标通常使用 `size_t` 类型，`size_t` 是机器相关的无符号类型，定义在 `cstddef` 头文件中。

数组也可以用 `range for` 来遍历。

``` cpp
for (auto i: scores) {
    std::cout << i;
}
```

直接用下标检测前一定要检查下标是否在合理范围内。

## 数组与指针

使用数组时，编译器会将其转换成指针。

``` cpp
int num[10];
int *p = num; // 等价于 int *p = &num[0];
```

## 数组与 `auto` / `decltype`

在 `auto` 中也会把数组看作指针，使用 `auto` 引用则正常。

``` cpp
auto p2(num); // p2 是 int*，等价于 int *p2 = &num[0];
```

但是使用 `decltype` 时数组不会转换成指针。

``` cpp
int num[10], ival;

decltype(num) num1[10]; // 数组而非指针
decltype(num) *p = &ival; // 非法
```

> 注意数组不是指针，只是大部分情况下会被当成指针处理！

## 指针与迭代器

数组的指针支持迭代器的所有运算。

获取数组的尾后指针需要用数组尾后元素的地址。

``` cpp
int num[10];
int *end = &num[10];
```

### `std::begin()` 与 `std::end()`

可以使用 `std::begin` 与 `std::end` 来获取头指针与尾后指针，这两个函数定义在 `iterator` 头文件中。

注意尾后指针不能被解引用。

``` cpp
int num[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
for (auto beg = std::begin(num), end = std::end(num); beg != end; ++beg) {
    std::cout << *beg;
}
std::cout << std::endl;
```

### 指针运算

指针还支持相加相减等操作（对于空指针和非数组指针也可以）。

``` cpp
int num[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
int *p = num + 4; // 等价于 int *p = &num[4];
```

两个指针相减的结果类型为 `ptrdiff_t`，也定义在 `cstddef` 头文件中，是一种带符号类型。

用指针遍历可以用比较运算符，如 `while (b < e)`。

### 下标和指针

使用解引用和指针运算时应注意使用括号

``` cpp
int ia[] = {0, 1, 2, 3, 4};
int ival = *(ia + 2); // 等价于 int ival = ia[2];
int ival2 = *ia + 2; // 等价于 int ival2 = ia[0] + 2;

```

标准库类型的下标运算不允许处理负值，但是数组的下标可以为负值。

``` cpp
int ia[] = {0, 1, 2, 3, 4};
int *p = ia + 2;
int j = p[1]; // j = ia[3];
int k = p[-1]; // k = ia[1];
```

> 数组变为指针时不能使用 `range for` 进行遍历，也不能用 `std::begin()`、`std::end()`。
>
> 因为编译器在编译期无法确定数组大小。

## C 风格字符串

字符串字面值也是 C 风格字符串，注意结尾有 `\0`。

### `cstring` 函数

| 函数             | 作用                                                  |
| ---------------- | ----------------------------------------------------- |
| `strlen(s)`      | 返回长度，不包括 `\0`                                 |
| `strcmp(s1, s2)` | 若 `s1>s2` 返回正值，若 `s1==s2` 返回 0，否则返回负值 |
| `strcat(s1, s2)` | 将 s2 连接到 s1 后面，并返回 s1                       |
| `strcpy(s1, s2)` | 将 s2 拷贝到 s1，并返回 s1                            |

注意定义时必须包含 `\0`，因此定义如 `char ch[] = {'C', 'p', 'p'}` 不能使用这些函数。

使用 `strcat` 与 `strcpy` 时必须保证数组大小足够存放结构。

### `cstring` 与 `std::string`

可以直接给 `std::string` 对象赋值 `cstring`，但是不可以反过来做。可以用 `s.c_str()` 将 `std::string` 转换成 `cstring` 并赋值给字符指针。

``` cpp
std::string s = "Hello";
char *str = s; // 非法
const char *str2 = s.c_str(); // c_str 返回的是一个指针，类型为 const char *
```

如果后续操作改变了 `s` 的值，那么之前的 `str2` 就有可能失效，所以最好复制一份整个数组。

## 数组与 `std::vector`

同样，也可以用数组来初始化 `std::vector`。

``` cpp
int arr[] = {0, 1, 2, 3, 4, 5};
vector<int> ivec(std::begin(arr), std::end(arr));
vector<int> ivec2(arr+1, arr+3); // 结果为 arr[1] 与 arr[2]

// vector 初始化数组（vector 内部空间连续）
memcpy(arr, &v[0], v.size()*sizeof(int))
```

## 多维数组

C++ 中的多维数组其实是数组的数组。

### 初始化

``` cpp
int ia[2][2] = {
    {0, 1},
    {2, 3}
};

int ia2[2][2] = {0, 1, 2, 3}; // 两种形式等价
int ia3[2][2] = { {0}, {1} }; // 仅声明行首元素
int ia4[2][2] = {0, 1}; //仅声明第一行
```

### 访问与遍历

用下标访问多维数组时，若下标维度比数组维度少，则返回一个内层数组。

``` cpp
for (size_t i = 0; i != rowCnt; ++i) {
    for (size_t j = 0; j != colCnt; ++j) {
        ia[i][j] = i * colCnt + j;
    }
}
```

### `range for` 遍历多维数组

可以使用 `range for` 来遍历多维数组。

``` cpp
for (auto &row: ia) { // 注意外层也要引用
    for (auto &col: row) {
        col = ++cnt;
    }
}
```

若不想改变数组的元素，应该把循环变量声明成 `const auto &row: ia`。

外层循环变量一定要设置为 `auto` 的引用类型，否则 `auto` 会把数组识别为指针。

### 指针与多维数组

多维数组名转换得到的指针指向内层数组，而非元素。

``` cpp
int ia[3][4];
int (*p)[4] = ia;

for (int (*p)[4] = a; p != ia + 3; ++p) {
    for (int *q = *p; q != p + 4; ++q) {
        std::cout << *q;
    }
}
```

### 多维数组与 `auto` / `decltype`

使用 `auto` 或者 `decltype`，可以用指针遍历数组。

``` cpp
int ia[3][4];

for (auto p = ia; p != ia + 3; ++p) { // 这里也可以改成 std::begin, std::end
    for (auto q = *p; q != *p + 4; ++q) { // *p 是一个数组
        std::cout << *q << ' ';
    }
}
```

### 类型别名简化多维数组指针

``` cpp
using int_array = int[4];
typedef int int_array[4]; // 等价形式

for (int_array *p = ia; p != ia + 3; ++p) {
    for (int *q = *p; q != *p + 4; ++q) {
        cout << *q << ' ';
    }
}
```
