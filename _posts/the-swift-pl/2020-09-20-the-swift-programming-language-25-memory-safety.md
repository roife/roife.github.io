---
layout: "post"
title: "「The Swift PL」 25 Memory Safety"
subtitle: "内存安全"
author: "roife"
date: 2020-09-20

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Memory Safety

默认情况下，Swift 会阻止代码中的不安全行为。如变量未初始化，数组越界。但是仍然可能遇到内存冲突。

# Understanding Conflicting Access to Memory

对同一内存地址的多个访问如果同时发生，就有可能造成不一致的行为。尤其是并发的代码与多线程中的代码。

## Characteristics of Memory Access

符合下面情况的两个访问可能会发生冲突：
- 有一个写访问
- 访问统一存储地址
- 访问在时间线上有重叠

# Conflicting Access to In-Out Parameters

函数会对 In-Out 参数进行长期写访问，在所有非 In-Out 参数处理完开始，到函数执行完毕为止。
对于多个 In-Out 参数，写访问开始的顺序和参数列表一致。

如，对于访问 In-Out 传递的变量。

```swift
var stepSize = 1

func increment(_ number: inout Int) {
    number += stepSize
}

increment(&stepSize)
```

向多个 In-Out 参数传入同一变量也会产生冲突（同时进行两个写访问）：

```swift
func balance(_ x: inout Int, _ y: inout Int) {
    let sum = x + y
    x = sum / 2
    y = sum - x
}
var playerOneScore = 42
var playerTwoScore = 30
balance(&playerOneScore, &playerOneScore)
```

注意操作符也是函数，对于含有 In-Out 参数的操作符进行重复传递也会发生冲突。

# Conflicting Access to self in Methods

在 methods 中访问 `self` 相当于将 `self` 作为 In-Out 参数传入。

```swift
struct Player {
    var health: Int

    mutating func shareHealth(with teammate: inout Player) {
        balance(&teammate.health, &health)
    }
}

var oscar = Player(health: 10)
oscar.shareHealth(with: &oscar)
```

# Conflicting Access to Properties

一个 tuple 是一个独立的 value type 变量，同时对 tuple 的不同部分写访问也会产生冲突。

```swift
var playerInformation = (health: 10, energy: 20)
balance(&playerInformation.health, &playerInformation.energy)
// 错误：playerInformation 的属性访问冲突
```

但是如果 structures 是局部变量，那么可以重叠访问：

```swift
func someFunction() {
    var oscar = Player(name: "Oscar", health: 10, energy: 10)
    balance(&oscar.health, &oscar.energy)  // 正常
}
```

遵循以下规则可以避免对于 properties of structures 的重叠访问：
- 访问实例的 stored properties，而非 computed properties 或 classes 的 properties
- structures 是 local 的
- structures 没有被 closures 捕获，或者只被 non-escaping closures 捕获了
