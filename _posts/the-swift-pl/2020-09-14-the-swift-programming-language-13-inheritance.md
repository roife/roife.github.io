---
layout: "post"
title: "「The Swift PL」 13 Inheritance"
subtitle: "继承"
author: "roife"
date: 2020-09-14

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Defining a Base Class

所有的类（Classes）都可以当父类。

```swift
class Vehicle {
    var currentSpeed = 0.0
    var description: String {
        // ...
    }
    func makeNoise() {
        // ...
    }
}

let someVehicle = Vehicle()
```

# Subclassing

```swift
class Bicycle: Vehicle {
    var hasBasket = false
}
```

子类会继承父类所有特性。

# Overriding

子类可以 override 父类的 mothods、properties、subscrpits。

在需要重写的特性前需要加上 `override` 关键字。

## Accessing Superclass Methods, Properties, and Subscripts

即使子类覆盖了父类的特性，也可以通过 `super` 访问父类版本。

- `super.someMethod()`
- `super.someProperty`
- `super[someIndex]`

## Overriding Methods

```swift
class Train: Vehicle {
    override func makeNoise() {
        // ...
    }
}
```

## Overriding Properties

Properties 进行 override 时要把名字和类型都写出来

`let` 修饰的 properties 不能通过继承修改。

### Overriding Property Getters and Setters

Stored 和 Computed Properties 都可以 override 提供 `getter` 和 `setter`。

可以把只读 properties 重写为读写的，但是读写的不能 override 为只读的。

如果重写属性提供了 `setter` 那么也一定要提供 `getter`，如果不想重写可以直接用 `super.someProperty`。

```swift
class Car: Vehicle {
    override var description: String {
        // ...
    }
}
```

### Overriding Property Observers

可以通过 override 添加 property observers。

不可以为常量或者只读 Computed Properties 添加 property observers（它们的值不会改变）。
同时 `setter` 和 property observers 只能提供一个，因为 `setter` 本身就可以起到 observers 的作用。

```swift
class AutomaticCar: Car {
    override var currentSpeed: Double {
        didSet {
            gear = Int(currentSpeed / 10.0) + 1
        }
    }
}
```

# Preventing Overrides

通过 `final` 可以防止 override，如 `final var` 等。

通过 `final class` 可以防止 Classes 被继承。
