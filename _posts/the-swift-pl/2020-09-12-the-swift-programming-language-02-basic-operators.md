---
layout: "post"
title: "「The Swift PL」 02 Basic Operators"
subtitle: "运算符"
author: "roife"
date: 2020-09-12

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Assignment Operator

赋值运算允许 tuple 的 decomposed 运算。

```swift
let (x, y) = (1, 2)
```

赋值运算不返回值。

```swift
if x = y {
    // invalid
}
```

# Arithmetic Operators

Swift 中的数值运算不允许溢出。

取余运算的符号和被除数相同。

# Unary Operator

Unary Operator 和数字之间不能有空格。

# Compound Assignment Operators

复合赋值运算（`+=` 等）也不返回值。

# Comparison Operators

除了普通的比较，Comparison Operators 也可以按照字典序比较两个类型相同的 tuple（元素数量不能大于 7 个）。

Booleans 不能被比较。

除此之外，Swift 还提供了 Identity Operators (`===` 和 `!==`).

# Ternary Conditional Operator

`?:` 建议不要复合使用。

```swift
let contentHeight = 40
let hasHeader = true
let rowHeight = contentHeight + (hasHeader ? 50 : 20)
```

# Nil-Coalescing Operator

`a ?? b` 如果 Optional a 非 nil 则返回 a，否则返回 b，等价于 `a != nil ? a! : b`，其中 b 的类型必须和 a 的内部类型匹配。并且这个运算符是短路的。

```swift
let defaultColorName = "red"
var userDefinedColorName: String?   // defaults to nil

var colorNameToUse = userDefinedColorName ?? defaultColorName
```

# Range Operators

## Closed Range Operator

生成 `[a, b]`。

```swift
for index in 1...5 {
    print("\(index) times 5 is \(index * 5)")
}
// 1 times 5 is 5
// 2 times 5 is 10
// 3 times 5 is 15
// 4 times 5 is 20
// 5 times 5 is 25
```

## Half-Open Range Operator

生成 `[a, b)`。

```swift
let names = ["Anna", "Alex", "Brian", "Jack"]
let count = names.count
for i in 0..<count {
    print("Person \(i + 1) is called \(names[i])")
}
// Person 1 is called Anna
// Person 2 is called Alex
// Person 3 is called Brian
// Person 4 is called Jack
```

## One-Sided Ranges

One-Sided Ranges 删掉了一边的数字，表示“到头为止”。

Closed Range Operator 和 Half-Open Range Operator 都有 One-Sided 的形式。

```swift
let names = ["Anna", "Alex", "Brian", "Jack"]
for name in names[2...] {
    print(name)
}
// Brian
// Jack

for name in names[...2] {
    print(name)
}
// Anna
// Alex
// Brian

for name in names[..<2] {
    print(name)
}
// Anna
// Alex
```

One-Sided Ranges 也可以不用作下标，此时如果是循环那么要注意添加中止条件。

```swift
let range = ...5
range.contains(7)   // false
range.contains(4)   // true
range.contains(-1)  // true
```

# Logical Operators

Logical Operators 都是短路的。

Swift 中的 `&&` 和 `||` 都是左结合的。
