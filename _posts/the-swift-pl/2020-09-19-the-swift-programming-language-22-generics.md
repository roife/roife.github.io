---
layout: "post"
title: "「The Swift PL」 22 Generics"
subtitle: "泛型"
author: "roife"
date: 2020-09-19

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Generic Functions

```swift
func swapTwoValues<T>(_ a: inout T, _ b: inout T) {
    let temporaryA = a
    a = b
    b = temporaryA
}
```

泛型函数使用 placeholder type name（即 `T`），而不是 actual type name（比如 `Int`）。拥有相同 placeholder type name 的参数必须拥有相同的类型。

# Type Parameters

placeholder type name 是一个类型参数，用尖括号括起来。
可以提供多个类型参数，如 `f<T, E>`。

# Naming Type Parameters

一般类型参数都有特殊名称，如 `Dictionary<Key, Value>`，`Array<Element>`。

类型参数应该使用首字母大写的驼峰命名法。

# Generic Types

Swift 允许自定义泛型类型，如 `Array`。

```swift
struct Stack<Element> {
    var items = [Element]()
    mutating func push(_ item: Element) {
        items.append(item)
    }
    mutating func pop() -> Element {
        return items.removeLast()
    }
}

var stackOfStrings = Stack<String>()
stackOfStrings.push("uno")
stackOfStrings.push("dos")
```

# Extending a Generic Type

对泛型进行拓展时，不需要将类型参数作为定义的一部分，而且类型参数可以直接在扩展中使用。

```swift
extension Stack {
    var topItem: Element? {
        return items.isEmpty ? nil : items[items.count - 1]
    }
}
```

# Type Constraints

Type Constraints 可以限制类型参数继承自某个类，或者遵守特定的 protocols。

## Type Constraint Syntax

```swift
func someFunction<T: SomeClass, U: SomeProtocol>(someT: T, someU: U) {
    // 这里是泛型函数的函数体部分
}
```

如要求类型拥有 `==` 操作时，可以约束其遵循 `Equatable` 协议。

```swift
func findIndex<T: Equatable>(of valueToFind: T, in array:[T]) -> Int? {
    for (index, value) in array.enumerated() {
        if value == valueToFind {
            return index
        }
    }
    return nil
}
```

# Associated Types

Associated Types 作为 protocol 中某个类型的 placeholder，其实际类型会在 protocol 被遵循时才确定，用 `associatedtype` 指定。

如在协议 `Container` 中，容器内元素类型 `Item` 事先不知道，可以被实现为 associated type。在遵循 protocol 时，可以用 `typealias` 指定类型（也可以不指定，让 Swift 进行 type inference）。

```swift
protocol Container {
    associatedtype Item
    mutating func append(_ item: Item)
    subscript(i: Int) -> Item { get }
}

struct IntStack: Container {
    // ...
    typealias Item = Int
    mutating func append(_ item: Int) {
        self.push(item)
    }
    subscript(i: Int) -> Int {
        return items[i]
    }
}

struct Stack<Element>: Container {
    // ...
    // Swift 会自动推断 Item 为 Element
    mutating func append(_ item: Element) {
        self.push(item)
    }
    var count: Int {
        return items.count
    }
    subscript(i: Int) -> Element {
        return items[i]
    }
}
```

## Extending an Existing Type to Specify an Associated Type

即 Adding Protocol Conformance with an Extension。

```swift
extension Array: Container {}
```

## Adding Constraints to an Associated Type

```swift
protocol Container {
    associatedtype Item: Equatable
    // ...
}
```

## Using a Protocol in Its Associated Type’s Constraints

可以让 associated types 遵循自己所在的 protocol。

```swift
protocol SuffixableContainer: Container {
    associatedtype Suffix: SuffixableContainer where Suffix.Item == Item
    func suffix(_ size: Int) -> Suffix
}

// 这里并不意味着 Suffix 和 Suffix Container 的类型相同，只要符合 where 的条件即可

extension IntStack: SuffixableContainer {
    func suffix(_ size: Int) -> Stack<Int> {
        // ...
    }
    // 推断 suffix 结果是 Stack<Int>。
}
```

# Generic Where Clauses

`where` 紧跟在类型参数列表之后，可以添加多个条件来为类型添加约束（使类型遵从某个特定的 protocol，或者两个类型相等），一般用于 associated types。

```swift
func allItemsMatch<C1: Container, C2: Container>
    (_ someContainer: C1, _ anotherContainer: C2) -> Bool
    where C1.Item == C2.Item, C1.Item: Equatable {
        // ...
}

// someContainer 是一个 C1 类型的容器。
// anotherContainer 是一个 C2 类型的容器。
// someContainer 和 anotherContainer 包含相同类型的元素。
// someContainer 中的元素可以通过不等于操作符（!=）来检查它们是否相同。
```

# Extensions with a Generic Where Clause

在 extension 中为类型加入约束，可以限定 extension 的生效条件。

```swift
extension Stack where Element: Equatable {
    func isTop(_ item: Element) -> Bool {
        guard let topItem = items.last else {
            return false
        }
        return topItem == item
    }
}

extension Container where Item == Double {
    func average() -> Double {
        var sum = 0.0
        for index in 0..<count {
            sum += self[index]
        }
        return sum / Double(count)
    }
}
```

# Contextual Where Clauses

类似于在 extension 中为扩展提出类型约束，也可以在方法中单独声明约束。这种方法可以减少重复定义 extension。

```swift
extension Container {
    func average() -> Double where Item == Int {
        // 只有 Item 为 Int 时才可用
    }
    func endsWith(_ item: Item) -> Bool where Item: Equatable {
        // 只有 Item 遵循 Equatable 时才可用
    }
}
```

# Associated Types with a Generic Where Clause

定义 associated types 时也可以用 `where` 添加类型约束。

```swift
protocol Container {
    // ...
    associatedtype Iterator: IteratorProtocol where Iterator.Element == Item
    func makeIterator() -> Iterator
}
```

继承时也可以用 `where` 添加约束。

```swift
protocol ComparableContainer: Container where Item: Comparable { }
```

# Generic Subscripts

```swift
extension Container {
    subscript<Indices: Sequence>(indices: Indices) -> [Item]
        where Indices.Iterator.Element == Int {
            var result = [Item]()
            for index in indices {
                result.append(self[index])
            }
            return result
    }
}
```
