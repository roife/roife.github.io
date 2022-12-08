---
layout: "post"
title: "「The Swift PL」 28 Concurrency"
subtitle: "async 与 await"
author: "roife"
date: 2022-11-03

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Defining and Calling Asynchronous Functions

异步方法在运行中的任意位置能被 suspended。异步方法只需要在函数头部加上 `async` 即可（如果同时还有 `throws`，则 `async` 在前）。

```swift
func listPhotos(inGallery name: String) async -> [String] {
    let result = // 省略一些异步网络请求代码
    return result
}
```

调用异步方法时，函数的执行会 suspends（即让出 CPU）直到这个异步方法返回。因此需要在调用前增加 `await` 关键字来标记此处为 suspension point。在两个 suspension point 之间的代码会顺序执行，不可被打断。

```swift
let photos = await listPhotos(inGallery: "Vacation")
```

在程序中只有特定的地方才能调用 asynchronous functions：
- 异步方法
- 带有 `@main` 标记的 structure、class 或 enumeration 中的 static `main()` 方法
- Unstructured child task

# Asynchronous Sequences

异步序列是一种异步的迭代器，需要遵守 `AsyncSequence` protocol，可以用 `for await` 循环来迭代，每轮迭代的开始可能会 suspend。

```swift
let handle = FileHandle.standardInput
for try await line in handle.bytes.lines {
    print(line)
}
```

# Calling Asynchronous Functions in Parallel

多个异步方法可以并发执行，只需要在定义函数调用的返回值时使用 `async` 关键字，然后在每次使用返回值前加 `await` 即可。

```swift
async let firstPhoto = downloadPhoto(named: photoNames[0])
async let secondPhoto = downloadPhoto(named: photoNames[1])
async let thirdPhoto = downloadPhoto(named: photoNames[2])
​
let photos = await [firstPhoto, secondPhoto, thirdPhoto]
```

- 需要立即使用异步方法的返回值时，用 `await` 来调用异步函数
- 短时间内并不需要异步函数的结果时，用 `async-let` 来保证并发性

# Tasks and Task Groups

Task 是程序中可以并发执行的工作单元，所有的异步方法都属于一个 task。此外，也能创建一个 task group，然后向其中添加 tasks。Task 是按一定层级排列的，一个 task 可以创建多个 child task，且 task group 和 task 之间有明确的父子关系，这种方式称为 **structured concurrency**。在这种情况下，Swift 能在编译期自动处理一些 task 之间的行为，例如 propagating cancellation 等。

## Unstructured Concurrency

Unstructured task 并没有 parent task，因此可以更灵活地操作，但是会影响安全性。

如果要创建一个在当前 actor 上运行的 unstructured task，需要用 `Task.init(priority:operation:)`。如果要创建一个不在当前 actor 上运行的 unstructured task（detached task），需要用 `Task.detached(priority:operation:)`。

## Task Cancellation

Swift 中的并发使用 cooperative cancellation 模型，task 可以检查自己是否被取消了。如果被取消了，task 可以采取以下操作：
- 抛出异常，如 `CancellationError` 等
- 返回 `nil` 或者 empty collection
- 返回完成一半的工作

如果 task 取消会返回 `CancellationError`，则可以用 `Task.checkCancellation()` 来检查是否被取消了。也可以用 `Task.isCancelled` 来检查是否被取消了。

手动执行扩散取消可以用 `Task.cancel()`。

# Actors

Actors 可以在并发代码间共享信息。Actor 的语法类似于 class，并且也是一个 reference type。但是 actor 在一个时间点内只允许一个 task 访问它，因此可以保证 actor 的状态不会被多个 task 同时修改。

可以用 `actor` 关键字来引入一个 actor。

```swift
actor Counter {
    var count = 0
    func increment() {
        count += 1
    }
    func decrement() {
        count -= 1
    }
}
```

在外部访问 actor 中的属性或方法时，需要使用 `await` 来标记 suspension point。而在 actor 内部则不需要。

```swift
let counter = Counter()
await counter.increment()

print(await counter.count)
```

# Sendable Types

Task 或 Actor 中可变的部分称为 Concurrency domain。一些类型的数据不能在 Concurrency domain 中使用，因为它们可能会被多个 task 同时修改。能够在 Concurrency domain 中使用的类型称为 Sendable type。而前面的例子用的都是简单的 value type，满足并发安全的条件。

通过实现 `Sendable` protocol 可以将某个类型标记为 Sendable type。实现 `Sendable` protocol 的类型不需要实现特定的方法，但是必须满足以下条件：
- 该类型为 value type，且可变的部分由 sendable 数据构成
- 该类型不包含可变状态，且不可变状态由 sendable 数据构成
- 该类型的可变状态是确保安全的

部分类型总是 sendable type，如只有 sendable properties 的 structures，或者只有 sendable associated values 的 enumerations。