---
layout: "post"
title: "「The Swift PL」 17 Error Handling"
subtitle: "错误处理"
author: "roife"
date: 2020-09-15

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Representing and Throwing Errors

错误用 `Error` protocol 的类型的值表示，一般用 enumerations 表示。

```swift
enum VendingMachineError: Error {
    case invalidSelection
    case insufficientFunds(coinsNeeded: Int)
    case outOfStock
}
```

抛出错误用 `throw` 语句。

```swift
throw VendingMachineError.insufficientFunds(coinsNeeded: 5)
```

# Handling Errors

Swift 中没有 unwinding the call stack 的过程，所以 `throw` 的开销很低。

调用可能会抛出错误的函数前，要加上 `try`、`try?`、`try!` 关键字。

Swift 有 4 种处理错误的方式。

## Propagating Errors Using Throwing Functions

在函数声明的参数之后加上 `throw` 关键字，使之成为 throwing function。

```swift
func canThrowErrors() throws -> String
```

只有 throwing functions 才能传递错误。

```swift
func vend(itemNamed name: String) throws {
        guard let item = inventory[name] else {
            throw VendingMachineError.invalidSelection
        }

        guard item.count > 0 else {
            throw VendingMachineError.outOfStock
        }

        guard item.price <= coinsDeposited else {
            throw VendingMachineError.insufficientFunds(coinsNeeded: item.price - coinsDeposited)
        }

        // ...
    }
```

被抛出的错误有两种解决方案：用 `do-catch`、`try?`、`try!` 解决；或将错误传递出去。

## Handling Errors Using Do-Catch

错误匹配的过程中可以使用 pattern matching。

```swift
do {
    try expression
    statements
} catch pattern 1 {
    statements
} catch pattern 2 where condition {
    statements
} catch pattern 3, pattern 4 where condition {
    statements
} catch {
    statements
}
```

如果上面所有的 `catch` 语句都没有捕获错误，那么错误会在最后一条 `catch` 中捕获，并赋值给 `error` 变量。

如果 `do-catch` 语句没有捕获错误，那么错误会跳出作用域抛出。如果错误到达顶层作用域还没有被捕获，则会发生运行时错误。不会抛出错误的函数必须用 `do-catch` 语句处理错误。

## Converting Errors to Optional Values

`try?` 可以把错误转换成 Optional 类型处理，计算出错时返回 `nil`。

```swift
func someThrowingFunction() throws -> Int {
    // ...
}

// 等价写法
let x = try? someThrowingFunction()

let y: Int?
do {
    y = try someThrowingFunction()
} catch {
    y = nil
}
```

如一种用法：

```swift
func fetchData() -> Data? {
    if let data = try? fetchDataFromDisk() { return data }
    if let data = try? fetchDataFromServer() { return data }
    return nil
}
```

## Disabling Error Propagation

当保证函数不会发生错误时，用 `try!` 可以禁用错误（但是如果发生了错误，就会直接触发断言）。

```swift
let photo = try! loadImage(atPath: "./Resources/John Appleseed.jpg")
```

# Specifying Cleanup Actions

`defer` 会让代码在退出当前作用于时执行，包括 `return`、`break`、错误都会触发代码。

`defer` 内部不能包含控制转移语句，如 `break`、`return`、抛出错误。且`defer` 语句倒序执行（最后一个 `defer` 最先执行，第一个最后执行）。

```swift
func processFile(filename: String) throws {
    if exists(filename) {
        let file = open(filename)
        defer {
            close(file)
        }
        while let line = try file.readline() {
            // 处理文件。
        }
        // close(file) 会在这里被调用，即作用域的最后。
    }
}
```

# Rethrowing Functions and Methods

用 `rethrows` 声明的函数或者 methods 可以仅当在自身函数参数抛出错误时，才抛出错误（也就是说自身不能抛出错误）。

```swift
func someFunction(callback: () throws -> Void) rethrows {
    try callback()
}
```
