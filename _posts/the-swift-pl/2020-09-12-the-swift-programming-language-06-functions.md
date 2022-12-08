---
layout: "post"
title: "「The Swift PL」 06 Functions"
subtitle: "函数"
author: "roife"
date: 2020-09-12

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Defining and Calling Functions

函数的实参必须与函数参数表里参数的顺序一致。

```swift
func greet(person: String) -> String {
    let greeting = "Hello, " + person + "!"
    return greeting
}

print(greet(person: "Alice"))
```

# Function Parameters and Return Values

函数的参数默认为常量。

函数可以省略返回值（本质上返回了 `void`，即 `()`）。

```swift
func greet(person: String) {
    print("Hello, \(person)!")
}
greet(person: "Dave")
```

## Functions with Multiple Return Values

用 tuple 可以一次返回多个值。

```swift
func minMax(array: [Int]) -> (min: Int, max: Int) {
    var currentMin = array[0]
    var currentMax = array[0]
    // ...
    return (currentMin, currentMax)
}

let bounds = minMax(array: [8, -6, 2, 109, 3, 71])
print("min is \(bounds.min) and max is \(bounds.max)")
```

## Optional Tuple Return Types

注意 `(Int, Int)?` 和 `(Int?, Int?)` 的区别。

```swift
func minMax(array: [Int]) -> (min: Int, max: Int)? {
    if array.isEmpty { return nil }

    var currentMin = array[0]
    var currentMax = array[0]
    // ...
    return (currentMin, currentMax)
}

if let bounds = minMax(array: [8, -6, 2, 109, 3, 71]) {
    print("min is \(bounds.min) and max is \(bounds.max)")
}
// 打印“min is -6 and max is 109”
```

## Functions With an Implicit Return

如果整个函数体是一个单行表达式，那么可以隐式地返回这个表达式。

```swift
func greeting(for person: String) -> String {
    "Hello, " + person + "!"
}

print(greeting(for: "Dave"))
```

# Function Argument Labels and Parameter Names

每个函数参数都有一个 argument label 和 parameter name。Argument label 在调用时使用，parameter name 在函数实现中使用。

默认情况下会使用 parameter naems 作为 argument labels。

## Specifying Argument Labels

```swift
func someFunction(argumentLabel parameterName: Int) {
    // 在函数体内，parameterName 代表参数值
}
```

## Omitting Argument Labels

用 `_` 可以忽略 Argument Labels。

```swift
func someFunction(_ firstParameterName: Int, secondParameterName: Int) {

}
someFunction(1, secondParameterName: 2)
```

## Default Parameter Values

```swift
func someFunction(parameterWithoutDefault: Int, parameterWithDefault: Int = 12) {

}
someFunction(parameterWithoutDefault: 3, parameterWithDefault: 6) // parameterWithDefault = 6
someFunction(parameterWithoutDefault: 4) // parameterWithDefault = 12
```

通常会把 Default Parameter 放在参数列表的最后（不是必须的）。

## Variadic Parameters

在变量类型名后面加入 `...` 可以定义 Variadic Parameters，此时传入的是一个数组。

```swift
func arithmeticMean(_ numbers: Double...) -> Double {
    var total: Double = 0
    for number in numbers {
        total += number
    }
    return total / Double(numbers.count)
}

arithmeticMean(1, 2, 3, 4, 5)
```

一个函数可以有多个 variadic parameters。为了防止混淆，variadic parameters 后面的跟的第一个参数必须带上 argument label（argument label 使得 Swift 可以有多个可变参数）。

## In-Out Parameters

函数参数默认为常数，如果需要修改（即定义为引用）需要在类型前加上 `inout` 将其定义为 In-Out Parameters。

Variadic Parameters 不能定义为 In-Out Parameters，而且 In-Out Parameters 不能有 Default Value。

```swift
func swapTwoInts(_ a: inout Int, _ b: inout Int) {
    let temporaryA = a
    a = b
    b = temporaryA
}

swapTwoInts(&someInt, &anotherInt)
```

调用时需要加上 `&`。

# Function Types

函数的类型由函数的参数类型和返回类型组成。

```swift
func addTwoInts(_ a: Int, _ b: Int) -> Int {
    return a + b
}
// 类型为 (Int, Int) -> Int

func printHelloWorld() {
    print("hello, world")
}
// 类型为 () -> void
```

## Using Function Types

```swift
var mathFunction: (Int, Int) -> Int = addTwoInts
let anotherMathFunction = addTwoInts

func printMathResult(_ mathFunction: (Int, Int) -> Int, _ a: Int, _ b: Int) {
    print("Result: \(mathFunction(a, b))")
}
printMathResult(addTwoInts, 3, 5)
```

```swift
func stepForward(_ input: Int) -> Int {
    return input + 1
}
func stepBackward(_ input: Int) -> Int {
    return input - 1
}
func chooseStepFunction(backward: Bool) -> (Int) -> Int {
    return backward ? stepBackward : stepForward
}
```

# Nested Functions

嵌套函数对外界不可见。

```swift
func chooseStepFunction(backward: Bool) -> (Int) -> Int {
    func stepForward(input: Int) -> Int { return input + 1 }
    func stepBackward(input: Int) -> Int { return input - 1 }

    return backward ? stepBackward : stepForward
}
```

# Functions that Never Return

Swift 定义了 `Never` 类型，即永远不会返回（但是可以抛出错误）。
一般在 `guard` 的 `else` 分句中使用。
