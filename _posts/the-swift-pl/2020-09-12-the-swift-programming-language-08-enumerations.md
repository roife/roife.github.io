---
layout: "post"
title: "「The Swift PL」 08 Enumerations"
subtitle: "枚举类型"
author: "roife"
date: 2020-09-12

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Enumeration Syntax

```swift
enum CompassPoint {
    case north
    case south
    case east
    case west
}

enum Planet {
    case mercury, venus, earth, mars, jupiter, saturn, uranus, neptune
}
```

Swift 的枚举成员在被创建时不会被赋予一个默认的整型值，它们本身就是一个完备的值。

enum 类型可以被编译器推断，变量的类型已知时，赋值可以用简洁的语法省略类型。

```swift
var directionToHead = CompassPoint.west

directionToHead = .east // 已知类型
```

# Matching Enumeration Values with a Switch Statement

```swift
directionToHead = .south
switch directionToHead {
case .north:
    // ...
case .south:
    // ...
case .east:
    // ...
case .west:
    // ...
}
// Prints "Watch out for penguins"
```

用 switch 时必须考虑所有情况，或者用 `default` 涵盖遗漏情况。

# Iterating over Enumeration Cases

令 enum 遵循 CaseIterable Protocol，Swift 会自动生成 `allCases` 属性，用来遍历。

```swift
enum Beverage: CaseIterable {
    case coffee, tea, juice
}

for beverage in Beverage.allCases {
    print(beverage)
}
```

# Associated Values

枚举可以存储任意类型的值（类似于 C++ 中的 `std::variant`）。

```swift
enum Barcode {
    case upc(Int, Int, Int, Int)
    case qrCode(String)
}

var productBarcode = Barcode.upc(8, 85909, 51226, 3)
productBarcode = .qrCode("ABCDEFGHIJKLMNOP")
```

用 switch 可以提取出 associated values。

为了方便可以直接在成员名称前标注 `let` 或 `var`。

```swift

switch productBarcode {
case .upc(let numberSystem, let manufacturer, let product, let check):
    // ...
case .qrCode(let productCode):
    // ...
}

switch productBarcode {
case let .upc(numberSystem, manufacturer, product, check):
    // ...
case let .qrCode(productCode):
    // ...
}
```

# Raw Values

注意区分 Associated Values 和 Raw Values。Raw Values 始终不变，且必须唯一。

Raw Values 可以是字符串、整型、浮点型。

## Implicitly Assigned Raw Values

使用整型或者字符串作为 Raw Values 时，Swift 可以自动赋值。

设置为 Int 时，第一项默认为 0，剩下的逐次递增 1；设置为 String 时，Raw Values 默认为名称。

用 `enum.item.rawValue` 可以访问 Raw Values。

```swift
enum Planet: Int {
    case mercury = 1, venus, earth, mars, jupiter, saturn, uranus, neptune
}

enum CompassPoint: String {
    case north, south, east, west
}

let earthsOrder = Planet.earth.rawValue
// earthsOrder 值为 3

let sunsetDirection = CompassPoint.west.rawValue
// sunsetDirection 值为 "west"
```

## Initializing from a Raw Value

因为提供的 Raw Value 不一定存在，所以返回 Optional 类型。

```swift
let possiblePlanet = Planet(rawValue: 7)
```

# Recursive Enumerations

在枚举成员前加上 `indirect` 关键字。

```swift
enum ArithmeticExpression {
    case number(Int)
    indirect case addition(ArithmeticExpression, ArithmeticExpression)
    indirect case multiplication(ArithmeticExpression, ArithmeticExpression)
}

indirect enum ArithmeticExpression {
    case number(Int)
    case addition(ArithmeticExpression, ArithmeticExpression)
    case multiplication(ArithmeticExpression, ArithmeticExpression)
}
```

可以配合递归函数使用。

```swift
func evaluate(_ expression: ArithmeticExpression) -> Int {
    switch expression {
    case let .number(value):
        return value
    case let .addition(left, right):
        return evaluate(left) + evaluate(right)
    case let .multiplication(left, right):
        return evaluate(left) * evaluate(right)
    }
}

print(evaluate(product))
```
