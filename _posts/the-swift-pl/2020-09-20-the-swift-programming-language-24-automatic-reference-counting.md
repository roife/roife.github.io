---
layout: "post"
title: "「The Swift PL」 24 ARC"
subtitle: "自动引用计数（Automatic Reference Counting）"
author: "roife"
date: 2020-09-20

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Automatic Reference Counting

Swift 使用 ARC 来管理内存（主要是 classes）。本章手动处理 ARC 主要是为了解决一些编译器难以处理的引用问题。

# How ARC Works

创建新实例时，ARC 会分配内存存储信息，当其内存不再被使用时，会自动释放对象。这一过程使用引用计数实现，即将实例赋值给 properties，常量或者变量时，会自动创建一个 strong reference，在 strong reference 减到 0 前都不会释放。

# Strong Reference Cycles Between Class Instances

类对象有可能会互相持有对方的 strong reference 导致对象无法销毁，即造成 strong reference cycle。

```swift
// 一段 strong reference cycle 代码
class Person {
    var apartment: Apartment?
}

class Apartment {
    var tenant: Person?
}

var john: Person? = Person()
var unit4A: Apartment? = Apartment()

john!.apartment = unit4A
unit4A!.tenant = john

john = nil
unit4A = nil
// 此处对象仍然无法销毁
```

# Resolving Strong Reference Cycles Between Class Instances

Swift 提供了 weak reference（短周期）和 unowned reference（长周期）两种方法解决 strong reference cycle 的问题。

## Weak References

Weak References 不算做 strong references，所以不会阻止 ARC 销毁对象。使用 weak references 只要在声明的变量或者 properties 前面加上 `weak` 关键字。当变量被销毁时，ARC 会自动将其赋值为 `nil`，所以 weak references 的变量一般会被定义为 optional 类型。

```swift
class Person {
    var apartment: Apartment?
}

class Apartment {
    weak var tenant: Person?
}

var john: Person? = Person()
var unit4A: Apartment? = Apartment

john!.apartment = unit4A
unit4A!.tenant = john

john = nil
// 此时 unit4A 会被销毁，自动赋值为 nil
```

当 ARC 设置 weak reference 为 `nil` 时，不会触发 observer。

## Unowned References

在声明时加上 `unowned` 则成为一个 unowned reference。同样，unowned reference 也不会导致引用计数增加。

Unowned references 在对象被销毁后不会被自动赋值 `nil`，因此一般不被定义为 optional 类型。Unowned references 必须指向一个没有被销毁的实例，否则访问时会报错（可以用 `unowned(unsafe)` 规避报错，但是不能保证安全性）。

```swift
class Customer {
    var card: CreditCard?
    // ...
}

class CreditCard {
    unowned let customer: Customer
    // ...
}
```

## Unowned Optional References

可以将 unowned references 设置为 optional type，此时要确保对象释放时会手动将其设置为 `nil`（虽然从理论上说 optional types 是 value type，不能设置为 `unowned`）。

```swift
class Department {
    var courses: [Course]
    // ...
}

class Course {
    unowned var department: Department
    unowned var nextCourse: Course?
    // ...
}
```

## Unowned References and Implicitly Unwrapped Optional Properties

当允许两个 properties 都被设置为 `nil` 时，适合使用 weak references。

当只允许一个 property 被设置为 `nil`，另外一个永远不为 `nil` 时，适合使用 unowned references。

当两个 properties 都不允许设置为 `nil` 时，适合一个使用 unowned reference，另一个使用强制 decompose。

```swift
class Country {
    // ...
    var capitalCity: City!
    init() {
        self.capitalCity = City()
    }
}

class City {
    // ...
    unowned let country: Country
```

# Strong Reference Cycles for Closures

Closures 和 classes 一样，也是 reference type。所以当 closures 中使用了 classes 中的某个 properties 或者 methods，就会造成 strong reference cycle。

Swift 中使用 closure capture list 解决这个问题。Closure capture list 定义了捕获规则。

在 closures 中使用 `self.someProperty` 或者 `self.someMethod()` 时，会强制要求不能省略 `self`，防止不小心捕获 `self`。

## Defining a Capture List

闭包内可以直接引用 `self`，或者使用初始化的变量（如 `self.delegate`）。

```swift
lazy var someClosure = {
    [unowned self, weak delegate = self.delegate]
    (index: Int, stringToProcess: String) -> String in
        // ...
}
```

也可以不指定参数列表和返回类型。

```swift
lazy var someClosure = {
    [unowned self, weak delegate = self.delegate] in
    // 这里是闭包的函数体
}
```

## Weak and Unowned References

Closures 和捕获的实例总是互相引用并且总是同时销毁时，一般将闭包内的捕获定义为 unowned references。

```swift
class HTMLElement {
    let name: String
    let text: String?

    lazy var asHTML: () -> String = {
        [unowned self] in
        if let text = self.text {
            return "<\(self.name)>\(text)</\(self.name)>"
        } else {
            return "<\(self.name) />"
        }
    }
}
```
