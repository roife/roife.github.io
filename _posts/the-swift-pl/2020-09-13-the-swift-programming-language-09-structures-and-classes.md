---
layout: "post"
title: "「The Swift PL」 09 Structures and Classes"
subtitle: "类和结构体"
author: "roife"
date: 2020-09-13

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Comparing Structures and Classes

共同点：
- 定义 properties、methods、subscripts、initializers
- 使用 extension 和 protocol

不同点：Classes 还有以下功能
- Inheritance
- Type casting
- Deinitializers (Destructer)
- Reference counting

## Definition Syntax

```swift
struct SomeStructure {
    // structure definition goes here
}

class SomeClass {
    // class definition goes here
}
```

## Structure and Class Instances

```swift
let someResolution = Resolution()
let someVideoMode = VideoMode()
```

## Accessing Properties

```swift
print("The width of someResolution is \(someResolution.width)")
```

## Memberwise Initializers for Structure Types

所有 structures 都有 memberwise initializer，即手动指定实例的属性。Classes 没有。

```swift
let vga = Resolution(width: 640, height: 480)
```

# Structures and Enumerations Are Value Types

Structures 和 Enumerations 是 Value Types，复制或传递时会被拷贝。

# Classes Are Reference Types

Classes 是 Reference Types，复制和传递时只传递引用。

因此当 Class Type 被声明为常量时，可以修改实例的 properties，因为变量只存储了引用。

## Identity Operators

- `===`, `!==`：检查两个引用是否引用了用一个实例

```swift
if tenEighty === alsoTenEighty {
    print("tenEighty and alsoTenEighty refer to the same VideoMode instance.")
}
```

注意和 `==` 的区别，`==` 是类实现者定义的运算符，而 `===` 只能判断对象是否引用同一实例。

## Pointers

Swift 可以用 `UnsafePointer<Type>` 和 `UnsafeMutablePointer<Type>` 创建指针，但是并不推荐使用。
