---
layout: "post"
title: "「The Swift PL」 07 Closures"
subtitle: "闭包"
author: "roife"
date: 2020-09-12

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Closure Expressions

## Closure Expression Syntax

```swift
{ (parameters) -> ret-type in
    statements
}
```

Closure Expression 的参数可以是 In-Out，但是不能设定默认值。

注意函数和返回值类型都写在大括号内。

```swift
reversedNames = names.sorted(by: { (s1: String, s2: String) -> Bool in
    return s1 > s2
})
```

## Inferring Type From Context

将 closure 作为函数参数传入时，Swift 可以自动推断类型。

```swift
reversedNames = names.sorted(by: { s1, s2 in return s1 > s2 } )
```

## Implicit Returns from Single-Expression Closures

单行闭包表达式可以省略 `return`。

```swift
reversedNames = names.sorted(by: { s1, s2 in s1 > s2 } )
```

## Shorthand Argument Names

可以用 `$0`，`$1` 等直接调用参数，此时可以省略参数列表和 `in`。

```swift
reversedNames = names.sorted(by: { $0 > $1 } )
```

## Operator Methods

运算符也可以被当作 Closure Expression。

```swift
reversedNames = names.sorted(by: >)
```

# Trailing Closures

当 closure 是函数的做后一个参数时，closure 可以写在括号后面。

使用 Trailing Closures 时不用写出 label。

```swift
func someFunctionThatTakesAClosure(closure: () -> Void) {

}

// 以下是不使用尾随闭包进行函数调用
someFunctionThatTakesAClosure(closure: {

})

// 以下是使用尾随闭包进行函数调用
someFunctionThatTakesAClosure() {

}
```

如果闭包是函数的唯一参数，那么可以直接省略括号。

```swift
reversedNames = names.sorted() { $0 > $1 }
reversedNames = names.sorted { $0 > $1 }
```

一个函数可以有多个 Trailing Closures，此时可以省略第一个 Trailing Closures 的 label，后面的则要指出 label。

```swift
func loadPicture(from server: Server, completion: (Picture) -> Void, onFailure: () -> Void) {
    if let picture = download("photo.jpg", from: server) {
        completion(picture)
    } else {
        onFailure()
    }
}

loadPicture(from: someServer) { picture in
    someView.currentPicture = picture
} onFailure: {
    print("Couldn't download the next picture.")
}
```

# Capturing Values

闭包可以捕获上下文的常量或变量，即使离开作用域也能继续使用。

```swift
func makeIncrementer(forIncrement amount: Int) -> () -> Int {
    var runningTotal = 0
    func incrementer() -> Int {
        runningTotal += amount
        return runningTotal
    }
    return incrementer
}

// 每调用一次返回值，runningTotal 都会递增
let incrementByTen = makeIncrementer(forIncrement: 10)
incrementByTen()
// returns a value of 10
incrementByTen()
// returns a value of 20
```

捕获引用保证捕获后变量不会消失，每次运行时依旧存在，Swift 会自动进行内存管理。

如果重新获取一个新的 closure，则捕获的值也有一个全新的引用，即不同的闭包之间是独立的。

```swift
let incrementBySeven = makeIncrementer(forIncrement: 7)
incrementBySeven()
// returns a value of 7
```

# Closures Are Reference Types

将 Closures 赋值给了两个不同的常量或变量，两个值都会指向同一个闭包。

将 Closures 赋值给常量也不影响捕获值的改变。

# Escaping Closures

Escaping Closures 即在一个当作参数传入，但是在函数完成后还可以继续使用的 Closures（防止被销毁）。可以用 `@escaping` 声明。

```swift
var completionHandlers: [() -> Void] = []
func someFunctionWithEscapingClosure(completionHandler: @escaping () -> Void) {
    completionHandlers.append(completionHandler)
}
```

在 Escaping CLosures 中对于 `class` 使用 `self` 需要谨慎，因为这有可能会造成 strong reference cycle。
在 Escaping Closures 中捕获 `class` 的值需要显式指出 `self`（对于 `struct` 和 `enum` 则不需要）。

```swift
func someFunctionWithNonescapingClosure(closure: () -> Void) {
    closure()
}

class SomeClass {
    var x = 10
    func doSomething() {
        someFunctionWithEscapingClosure { self.x = 100 }
        someFunctionWithNonescapingClosure { x = 200 }
    }
}

let instance = SomeClass()
instance.doSomething()
print(instance.x)
// 打印出“200”

completionHandlers.first?()
print(instance.x)
// 打印出“100”
```

除此之外，也可以将 `self` 放入 capture list。

```swift
class SomeOtherClass {
    var x = 10
    func doSomething() {
        someFunctionWithEscapingClosure { [self] in x = 100 }
        someFunctionWithNonescapingClosure { x = 200 }
    }
}
```

虽然 `struct` 和 `enum` 不需要显式使用 `self`，但是它们不允许捕获 mutable 的变量。

```swift
struct SomeStruct {
    var x = 10
    mutating func doSomething() {
        someFunctionWithNonescapingClosure { x = 200 }  // Ok
        someFunctionWithEscapingClosure { x = 100 }     // Error
    }
}
```

# Autoclosures

Autoclosures 是自动创建的 Closures，不接受任何参数，用 `@autoclosure` 标记。用 Autoclosures 可以省略花括号，直接用表达式。如 `assert(condition:message:file:line:)` 中的 `condition`。

Autoclosures 会 lazy-evaluate，即被调用时再求值。

```swift
// customersInLine is ["Ewa", "Barry", "Daniella"]
func serve(customer customerProvider: @autoclosure () -> String) {
    print("Now serving \(customerProvider())!")
}
serve(customer: customersInLine.remove(at: 0))
// 打印“Now serving Ewa!”
```

同时使用 `@autoclosure` 和 `@escaping` 可以让 Autoclosures escape。

```swift
// customersInLine i= ["Barry", "Daniella"]
var customerProviders: [() -> String] = []
func collectCustomerProviders(_ customerProvider: @autoclosure @escaping () -> String) {
    customerProviders.append(customerProvider)
}
collectCustomerProviders(customersInLine.remove(at: 0))

print("Collected \(customerProviders.count) closures.") // 打印“Collected 2 closures.”

for customerProvider in customerProviders {
    print("Now serving \(customerProvider())!")
}
// 打印“Now serving Barry!”
// 打印“Now serving Daniella!”
```
