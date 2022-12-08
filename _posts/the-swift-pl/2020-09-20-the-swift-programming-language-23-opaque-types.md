---
layout: "post"
title: "「The Swift PL」 23 Opaque Types"
subtitle: "不透明类型"
author: "roife"
date: 2020-09-20

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Returning an Opaque Type

泛型允许调用方法时，方法的形参和返回值由调用者对实现者隐藏。Opaque Types 则恰好相反，将方法的类型由实现者对用户隐藏。
隐藏类型一方面有利于重构，另一方面也实现了更好的封装。Opaque returning type 用 `-> Some somType` 表示。

```swift
struct JoinedShape<T: Shape, U: Shape>: Shape {
    func draw() -> String {
        // ...
    }
}

struct Square: Shape {
    func draw() -> String {
        // ...
    }
}

func makeTrapezoid() -> some Shape { // 返回 opaque type
    // ...
    let trapezoid = JoinedShape( /*...*/ )
    return trapezoid
}

let trapezoid = makeTrapezoid() // 返回了一个 JoinedShape，但是用户可见的是 Shape, JoinedShape 被隐藏了
```

Opaque Types 也可以和泛型一起结合使用。

```swift
func flip<T: Shape>(_ shape: T) -> some Shape {
    return FlippedShape(shape: shape)
}
func join<T: Shape, U: Shape>(_ top: T, _ bottom: U) -> some Shape {
    JoinedShape(top: top, bottom: bottom)
}

let opaqueJoinedTriangles = join(smallTriangle, flip(smallTriangle))
print(opaqueJoinedTriangles.draw())
```

如果函数中有多个地方返回了 opaque types，那么他们的类型必须**保持一致**，仅仅是遵循统一个协议还不够。

# Differences Between Opaque Types and Protocol Types

返回 Opaque Types 和返回 protocol types 很像，其区别在于，Opaque Types 要保证类型一致性，而 protocols 不需要保证类型一致性，只要返回的类型遵从 protocol 即可。因此 protocols 更加灵活，opaque types 限制更强。

使用 protocol types 时进行了 type erasure，会丢失类型信息，而 opaque types 可以保存类型信息。这可能会导致**无法访问部分方法或属性**。

```swift
func protoFlip<T: Shape>(_ shape: T) -> Shape {
    return FlippedShape(shape: shape)
}

let protoFlippedTriangle = protoFlip(smallTriangle)
let sameThing = protoFlip(smallTriangle)
protoFlippedTriangle == sameThing  // 错误
```

如上，Shape protocol 中没有定义 `==` 运算符，所以比较时会出错。但是使用 opaque types 时，如果其具体类型的内部定义了 `==` 运算符，那么还可以继续使用。

Type Erasure 带来的另一个问题是**不适合操作嵌套**。如 `protoFlip(_:_)` 方法接受一个遵循 `Shape` protocol 的类型，而返回结果是一个 `Shape` 类型。由于 `Shape` 类型的值不遵循 `Shape` protocol，因此 `protoFlip(protoFlip(smallTriangle))` 是非法的。

相反 opaque types 保存了底层类型（只是不暴露），使得 Swift 能推断出原始类型。

同时，具有 associated types 的 protocol 不能作为返回类型，但是可以作为 opaque type 返回。
