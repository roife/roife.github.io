---
layout: "post"
title: "「The Swift PL」 12 Subscripts"
subtitle: "下标"
author: "roife"
date: 2020-09-14

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Subscripts

Subscripts 可以在 structures、classes、enumerations 中定义。

一个类型可以定义多个 subscripts 进行重载，每个 subscripts 也可以定义多维。

# Subscript Syntax

下标类似于 Computed Properties，用 `subscript` 声明。同样，如果不指定参数，`set` 可以直接用 `newValue` 访问。

```swift
subscript(index: Int) -> Int {
    get {
        // ...
    }
    set(newValue) {
      // ...
    }
}

subscript(index: Int) -> Int { // 只读的下标
    // ...
}
```

# Subscript Options

Subscripts 可以接受任意数量的入参，提供默认参数，但是不能使用 In-Out 参数。

```swift
struct Matrix {
    // ...
    subscript(row: Int, column: Int) -> Double {
        get {
            // ...
        }
        set {
            // ...
        }
    }
}

var matrix = Matrix(rows: 2, columns: 2)
matrix[0, 1] = 1.5
```

# Type Subscripts

在 `subscript` 前面写 `static` 可以定义 Type Subscripts。
Classes 可以用 `class` 替代 `static`，使得允许子类重写父类中的实现。

```swift
enum Planet: Int {
    case mercury = 1, venus, earth, mars, jupiter, saturn, uranus, neptune
    static subscript(n: Int) -> Planet {
        return Planet(rawValue: n)!
    }
}

let mars = Planet[4]
print(mars)
```
