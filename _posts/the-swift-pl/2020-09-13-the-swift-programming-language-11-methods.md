---
layout: "post"
title: "「The Swift PL」 11 Methods"
subtitle: "方法"
author: "roife"
date: 2020-09-13

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Methods

Structures、Classes、Enumerations 都可以定义 methods。

# Instance Methods

Instance Methods 就是属于特定实例的 methods，定义和函数一样。

```swift
class Counter {
    var count = 0
    func increment() {
        count += 1
    }
}

let counter = Counter()
counter.increment()
```

## The self Property

每个实例都有一个隐藏的 `self` 属性表示实例本身，可以在名字冲突时可以显式指出。

```swift
struct Point {
    var x = 0.0, y = 0.0
    func isToTheRightOf(x: Double) -> Bool {
        return self.x > x
    }
}
```

## Modifying Value Types from Within Instance Methods

Structures 和 Enumerations 是 Value Types，其 properties 默认不能修改，此时可以把 `mutating` 放到 `func` 前修饰。

```swift
struct Point {
    var x = 0.0, y = 0.0
    mutating func moveBy(x deltaX: Double, y deltaY: Double) {
        x += deltaX
        y += deltaY
    }
}
```

注意，仍然不可以对于**常量结构体**调用 `mutating` 方法。

## Assigning to self Within a Mutating Method

```swift
struct Point {
    var x = 0.0, y = 0.0
    mutating func moveBy(x deltaX: Double, y deltaY: Double) {
        self = Point(x: x + deltaX, y: y + deltaY)
    }
}
```

```swift
enum TriStateSwitch {
    case off, low, high
    mutating func next() {
        switch self {
        case .off:
            self = .low
        case .low:
            self = .high
        case .high:
            self = .off
        }
    }
}
```

# Type Methods

Type Methods 需要在 `func` 前加入 `static`。
可以为所有的 Structures、Classes、Enumerations 定义 Type Methods。
同样，Type Methods 需要在类型上调用，不能在实例上调用。

```swift
class SomeClass {
    static func someTypeMethod() {
        // ...
    }
}
SomeClass.someTypeMethod()
```

在 Classes 中，可以用 `class` 替代 `static`，从而支持子类对父类的方法进行 Override。

```swift
class SomeClass {
    class func someTypeMethod() {
        // ...
    }
}
SomeClass.someTypeMethod()
```

Type Methods 中的 `self` 指类型本身（而非实例）。

# callAsFunction

实现了 `callAsFunction` 方法的 classes、structures、enumerations 可以将其当作函数使用。

```swift
struct CallableStruct {
    var value: Int
    func callAsFunction(_ number: Int, scale: Int) {
        print(scale * (number + value))
    }
}
let callable = CallableStruct(value: 100)
callable(4, scale: 2)
```
