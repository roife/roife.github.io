---
layout: "post"
title: "「The Swift PL」 05 Control Flow"
subtitle: "控制流"
author: "roife"
date: 2020-09-12

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# For-In Loops

For-In Loops 可以用来遍历 Collection Types 或者 Ranges。

访问时也可以用 `_` 省略变量名。

```swift
for _ in 1...power {
    answer *= base
}
```

- `stride(from:to:by)` 创建跳跃性的区间，左闭右开
- `stride(from:through:by)` 创建跳跃性的区间，闭区间

```swift
let minutes = 60
let minuteInterval = 5
for tickMark in stride(from: 0, to: minutes, by: minuteInterval) {
    // 每 5 分钟渲染一个刻度线（0, 5, 10, 15 ... 45, 50, 55）
}

let hours = 12
let hourInterval = 3
for tickMark in stride(from: 3, through: hours, by: hourInterval) {
    // 每 3 小时渲染一个刻度线（3, 6, 9, 12）
}
```

# While and Repeat-While

```swift
while condition {

}

repeat {

} while condition
```

# Conditional Statements

## if

```swift
if condition {

} else if {

} else {

}
```

## switch

```swift
switch some value to consider {
case value 1:
    respond to value 1
case value 2,
    value 3:
    respond to value 2 or 3
default:
    otherwise, do something else
}
```

Switch 语句必须是完备的，所以一般需要 `default` 来包含遗漏的情况。

Swift 中的 switch 不会 Implicit Fallthrough，但是仍然可以用 break 提前退出 switch。

如果需要 Fallthrough，可以用 `fallthrough` 语句。

### Interval Matching

```swift
let approximateCount = 62
let countedThings = "moons orbiting Saturn"
let naturalCount: String
switch approximateCount {
case 0:
    // ...
case 1..<5:
    // ...
case 5..<12:
    // ...
default:
    // ...
}
```

### Tuples

用 `_` 可以当作占位符。

```swift
let somePoint = (1, 1)
switch somePoint {
case (0, 0):
    // ...
case (_, 0):
    // ...
case (0, _):
    // ...
default:
    // ...
}
```

### Value Bindings

用 `let` 在匹配的同时进行 decompose。

```swift
let anotherPoint = (2, 0)
switch anotherPoint {
case (let x, 0):
    // ...
case (0, let y):
    // ...
case let (x, y):
    // ...
}
```

注意这里没有 `default` 语句，因为最后一个 `case let (x, y)` 相当于 `default`。

### where

用 `where` 可以附加条件。

```swift
let yetAnotherPoint = (1, -1)
switch yetAnotherPoint {
case let (x, y) where x == y:
    // ...
case let (x, y) where x == -y:
    // ...
case let (x, y):
    // ...
}
```

### Compound Cases

一个 `case` 可以绑定多个模式。

用于 Value Bindings 时，所有的模式必须包含相同的值绑定，且绑定值的类型必须相同。

```swift
let stillAnotherPoint = (9, 0)
switch stillAnotherPoint {
case (let distance, 0), (0, let distance):
    print("On an axis, \(distance) from the origin")
default:
    print("Not on an axis")
}
// 输出“On an axis, 9 from the origin”
```

# Control Transfer Statements

常见的 Control Transfer Statements

- `continue`
- `break`
- `fallthrough`（仅用于 `case`)

## Labeled Statements

对于循环和条件语句，可以用 `label` 标记，便于使用 `break` 和 `continue` 快速退出。

```swift
label name: while condition {
     statements
}
```

```swift
gameLoop: while square != finalSquare {
    // ...
    switch square + diceRoll {
    case finalSquare:
        break gameLoop
    case let newSquare where newSquare > finalSquare:
        continue gameLoop
    default:
        // ...
    }
}
```

# Early Exit

`guard` 语句用于确保某个表达式必须为真，为真时继续执行，否则执行 `else`。`guard` 一定要加上一个 `else` 语句（`else` 里面一般通过返回值为 `Never` 的函数、`break`、`return`、`continue` 等语句来结束执行）。

```swift
func greet(person: [String: String]) {
    guard let name = person["name"] else {
        return
    }

    guard let location = person["location"] else {
        print("I hope the weather is nice near you.")
        return
    }

    // ...
}
```

# Checking API Availability

```swift
if #available(iOS 10, macOS 10.12, *) {
    // 在 iOS 使用 iOS 10 的 API，在 macOS 使用 macOS 10.12 的 API
} else {
    // 使用先前版本的 iOS 和 macOS 的 API
}
```

类似 `available` 还有 `unavailable`。

# Case Statements

在 `if`、`for`、`while`、`guard`、`for-in` 语句中均可以用 `case` 进行 pattern matching。

```swift
if case let Media.Movie(_, _, year) = m where year < 1888 {
  print("Something seems wrong: the movie's year is before the first movie ever made.")
}

for case let Media.Movie(title, director, year) in mediaList where director == "Chris Columbus" {
  print(" - \(title) (\(year))")
}
```
