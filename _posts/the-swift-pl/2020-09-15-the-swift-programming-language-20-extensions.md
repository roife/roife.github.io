---
layout: "post"
title: "「The Swift PL」 20 Extensions"
subtitle: "扩展"
author: "roife"
date: 2020-09-15

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Extensions

Extensions 可以给现有的 classes、structures、enumerations、protocols、generics 添加功能，并且不需要访问其源代码，其作用包括：
- 添加 computed properties
- 定义 methods，initializers，subscripts，nested types
- 使其 conform 一个 protocol
- 为 generics 添加 `where`

# Extension Syntax

```swift
extension SomeType {
    // ...
}

extension SomeType: SomeProtocol, AnotherProtocol {
    // ...
}
```

# Computed Properties

```swift
extension Double {
    var km: Double { return self * 1_000.0 }
    var m: Double { return self }
    var cm: Double { return self / 100.0 }
}

let aMarathon = 42.km + 195.m
print("A marathon is \(aMarathon) meters long")
```

注意，extension 不能添加 stored properties。

# Initializers

Extension 可以为 classes 创建 convenience initializers，但是不能创建 deinitializers 和 desganited initializers。

对于 value types，如果其所有 stored properties 都有默认值，而且没有任何的自定义 initializers，则可以在 extension 中定义 default initializers 和 memberwise initializers。

如果使用 extension 给另一个模块中的 structures 添加 initializers，则这个 initializer 只有在调用了该模块中原有的 initializer 后才能访问 `self`。

```swift
struct Size {
    var width = 0.0, height = 0.0
}
struct Point {
    var x = 0.0, y = 0.0
}
struct Rect {
    var origin = Point()
    var size = Size()
}

extension Rect {
    init(center: Point, size: Size) {
        // ...
    }
}
```

# Methods

```swift
extension Int {
    func repetitions(task: () -> Void) {
        for _ in 0..<self {
            task()
        }
    }
}

3.repetitions {
    print("Hello!")
}
```

## Mutating Instance Methods

```swift
extension Int {
    mutating func square() {
        self = self * self
    }
}
var someInt = 3
someInt.square()
// someInt 为 9
```

# Subscripts

```swift
extension Int {
    subscript(digitIndex: Int) -> Int {
        var decimalBase = 1
        for _ in 0..<digitIndex {
            decimalBase *= 10
        }
        return (self / decimalBase) % 10
    }
}
746381295[0]
// 返回 5
```

# Nested Types

```swift
extension Int {
    enum Kind {
        case negative, zero, positive
    }
    var kind: Kind {
        switch self {
        case 0:
            return .zero
        case let x where x > 0:
            return .positive
        default:
            return .negative
        }
    }
}
```
