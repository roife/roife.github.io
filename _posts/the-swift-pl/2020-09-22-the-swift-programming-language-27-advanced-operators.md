---
layout: "post"
title: "「The Swift PL」 27 Advanced Operators"
subtitle: "高级运算符操作"
author: "roife"
date: 2020-09-22

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Bitwise Operators

## Bitwise NOT Operator

```swift
let invertedBits = ~initialBits
```

## Bitwise AND Operator

```swift
let middleFourBits = firstSixBits & lastSixBits
```

## Bitwise OR Operator
```swift
let combinedbits = someBits | moreBits
```

## Bitwise XOR Operator

```swift
let outputBits = firstBits ^ otherBits
```

## Bitwise Left and Right Shift Operators

对于 `unsigned` 类型，用 `0` 填补空白位。
对于 `signed` 类型，用符号为填补空白位。

```swift
shiftBits << 1
```

# Overflow Operators

普通的四则运算符不允许 overflow，如果发生了就会报错。

- Overflow Addition: `&+`
- Overflow Substraction: `&-`
- Overflow Multiplication: `&*`

# Operator Methods

Classes 和 structures 可以 override 已有的运算符。

```swift
struct Vector2D {
    var x = 0.0, y = 0.0
}

extension Vector2D {
    static func + (left: Vector2D, right: Vector2D) -> Vector2D {
        return Vector2D(x: left.x + right.x, y: left.y + right.y)
    }
}

let vector = Vector2D(x: 3.0, y: 1.0)
let anotherVector = Vector2D(x: 2.0, y: 4.0)
let combinedVector = vector + anotherVector
```

## Prefix and Postfix Operators

Prefix Operators 如 `-a`，Postfix Operators 如 `b!`。

实现 prefix 和 postfix 运算符时要用 `prefix` 和 `postfix` 修饰。

```swift
extension Vector2D {
    static prefix func - (vector: Vector2D) -> Vector2D {
        return Vector2D(x: -vector.x, y: -vector.y)
    }
}
```

## Compound Assignment Operators

Compound Assignment Operators 要把左参数设置为 `inout`。

```swift
extension Vector2D {
    static func += (left: inout Vector2D, right: Vector2D) {
        left = left + right
    }
}
```

注意：不能对 `=` 和 `a ? b : c` 进行 override。

## Equivalence Operators

定义了 `==`，标准库定义了 `!=` 的默认实现。

定义 `==` 需要让自定义类型遵循 `Equatable` protocol。多数情况下，`==` 可以让 Swift 自动合成。

```swift
extension Vector2D: Equatable {
    static func == (left: Vector2D, right: Vector2D) -> Bool {
        return (left.x == right.x) && (left.y == right.y)
    }
}
```

# Custom Operators

新运算符要用 `operator` 在全局作用域定义，同时要指定 `prefix`, `infix`, `postfix`。

```swift
extension Vector2D {
    static prefix func +++ (vector: inout Vector2D) -> Vector2D {
        vector += vector
        return vector
    }
}

var toBeDoubled = Vector2D(x: 1.0, y: 4.0)
let afterDoubling = +++toBeDoubled
```

## Precedence for Custom Infix Operators

没有明确定义优先级的中缀运算符会被放入一个默认优先级组（`DefaultPrecedence`），其优先级高于 `a ? b : c`（`TernaryPrecedence`）。

```swift
infix operator +-: AdditionPrecedence // 和加法同级
extension Vector2D {
    static func +- (left: Vector2D, right: Vector2D) -> Vector2D {
        return Vector2D(x: left.x + right.x, y: left.y - right.y)
    }
}
```

也可以自定义 precedence group declaration。

```swift
precedencegroup 优先级组名称{
    higherThan: 较低优先级组的名称
    lowerThan: 较高优先级组的名称
    associativity: 结合性（left，right，none）
    assignment: 赋值性（bool）
}
```

# Expression Pattern

Pattern Matching 的过程实际上是调用了 `~=` 运算符进行匹配。因此 override `~=` 运算符也可以自定义匹配行为。

```swift
func ~=(pattern: String, value: Int) -> Bool {
    return pattern == "\(value)"
}

switch point {
case ("0", "0"):
    print("(0, 0) is at the origin.")
default:
    print("The point is at (\(point.0), \(point.1)).")
}
```

# Result Builders

Result Builder 是一种特殊的类型，他可以让你用命令式语句（`if` 和 `for`）更方便地来构建嵌套类型。

比如以下这个例子定义了一个 `Drawable` 协议，并且构建了一个 `Line` 类型，但是 `AllCaps` 的内容包括了一个选择项，看起来比较复杂：

```swift
protocol Drawable {
    func draw() -> String
}
struct Line: Drawable {
    var elements: [Drawable]
    func draw() -> String {
        return elements.map { $0.draw() }.joined(separator: "")
    }
}
struct Text: Drawable {
    var content: String
    init(_ content: String) { self.content = content }
    func draw() -> String { return content }
}
struct AllCaps: Drawable {
    var content: Drawable
    func draw() -> String { return content.draw().uppercased() }
}

let name: String? = "Ravi Patel"
let manualDrawing = Line(elements: [
    Text("Hello"),
    AllCaps(content: Text((name ?? "World") + "!")), // 看起来比较复杂
    ])

print(manualDrawing.draw())
```

Result Builder 可以让你用 `if-else` 的语法写这种选择结构。首先定义 `DrawingBuilder` 类型并加上属性 `@resultBuilder`，然后在里面定义 `buildBlock` 等特定的方法，Swift 会将命令式的 `if-else` 等转换成对这些方法的调用。

```swift
@resultBuilder
struct DrawingBuilder {
    static func buildBlock(_ components: Drawable...) -> Drawable {
        return Line(elements: components)
    }
    static func buildEither(first: Drawable) -> Drawable {
        return first
    }
    static func buildEither(second: Drawable) -> Drawable {
        return second
    }
}
```

使用 resultBuilder 时，只需要用它来修饰函数传入的参数，然后 Swift 就会自动将闭包转换成对应的数据。

```swift
func draw(@DrawingBuilder content: () -> Drawable) -> Drawable {
    return content()
}
func caps(@DrawingBuilder content: () -> Drawable) -> Drawable {
    return AllCaps(content: content())
}

func makeGreeting(for name: String? = nil) -> Drawable {
    let greeting = draw { // 会被改写
        Stars(length: 3)
        Text("Hello")
        Space()
        caps { // 会被改写
            if let name = name {
                Text(name + "!")
            } else {
                Text("World!")
            }
        }
        Stars(length: 2)
    }
    return greeting
}

// caps 语句会被改写成这个样子
let capsDrawing = caps {
    let partialDrawing: Drawable
    if let name = name {
        let text = Text(name + "!")
        partialDrawing = DrawingBuilder.buildEither(first: text)
    } else {
        let text = Text("World!")
        partialDrawing = DrawingBuilder.buildEither(second: text)
    }
    return partialDrawing
}
```

对于 `for` 循环，则应该使用 `buildArray` 方法。

```swift
extension DrawingBuilder {
    static func buildArray(_ components: [Drawable]) -> Drawable {
        return Line(elements: components)
    }
}
let manyStars = draw {
    Text("Stars:")
    for length in 1...3 {
        Stars(length: length)
    }
}
```