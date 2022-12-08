---
layout: "post"
title: "「The Swift PL」 21 Protocols"
subtitle: "协议"
author: "roife"
date: 2020-09-19

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Protocols

Protocols 定义了实现任务的 methods、properties 等。遵循某个 protocol 的 class、structure、enumeration 要为 protocol 中的要求提供对应的实现，即遵循（conform）这个 protocol。

Protocols 也可以被 extension 扩展。

# Protocol Syntax

```swift
protocol SomeProtocol {
    // 这里是协议的定义部分
}
```

```swift
struct SomeStructure: FirstProtocol, AnotherProtocol {
    // 这里是结构体的定义部分
}
```

如果 class 有父类，则父类要放在 protocols 之前。

```swift
class SomeClass: SomeSuperClass, FirstProtocol, AnotherProtocol {
    // 这里是类的定义部分
}
```

# Property Requirements

Protocols 不指定 properties 是 computed 还是 stored，只指定名称和类型，以及可读、可读可写性。

- 对于可读可写的 properties，不能被实现为常量或者只读 computed properties（但是可以被实现为常量）
- 对于可读的 properties，可以被实现为可读可写的

Protocols 总是用 `var` 声明，用 `static` 声明 type properties。

```swift
protocol SomeProtocol {
    var mustBeSettable: Int { get set } // 可读可写
    var doesNotNeedToBeSettable: Int { get } // 可读
    static var someTypeProperty: Int { get set }
}
```

# Method Requirements

在 protocols 中生命的 methods 不需要大括号。

不允许在 protocols 中为方法提供默认参数。

当允许方法改变 `self` 时，需要在 protocol 中用 `mutating` 修饰。在实现时 class 不用写 `mutating`，但是 structure 和 enumeration 必须写。

```swift
protocol RandomNumberGenerator {
    func random() -> Double
    static func someTypeMethod()
}
```

```swift
protocol Togglable {
    mutating func toggle()
}

enum OnOffSwitch: Togglable {
    case off, on
    mutating func toggle() {
        switch self {
        case .off:
            self = .on
        case .on:
            self = .off
        }
    }
}
```

# Initializer Requirements

```swift
protocol SomeProtocol {
    init(someParameter: Int)
}
```

## Class Implementations of Protocol Initializer Requirements

遵循 protocol 实现 initializers 时必须用 `required` 修饰（强制子类遵循协议，但是当 class 为 `final` 时可以不加）。

```swift
protocol SomeProtocol {
    init()
}

class SomeSuperClass {
    init() {
        // 这里是构造器的实现部分
    }
}

class SomeSubClass: SomeSuperClass, SomeProtocol {
    // 因为遵循协议，需要加上 required
    // 因为继承自父类，需要加上 override
    required override init() {
        // 这里是构造器的实现部分
    }
}
```

## Failable Initializer Requirements

- Protocols 中定义的 failable initializers 可以被实现为 `init?` 或 `init`
- Protocols 中定义的 nonfailable initializers 可以被实现为 `init` 或 `init!`

# Protocols as Types

Protocols 可以被当作一个 Type 使用，实际上是一个**existential type**，即 "there exists a type T such that T conforms to the protocol"。

- Protocols 可以作为函数、methods、initializers 的参数和返回类型
- 作为常量、变量、properties 的类型
- 作为 array、dictionary、其他 containers 的类型

当 protocol 作为类型时，可以被赋值为任何一个遵循该 protocol 的实例。如果要调用实例里除了 protocol 中定义的独有的方法，需要先进行 downcasting。

```swift
class Dice {
    let sides: Int
    let generator: RandomNumberGenerator // RandomNumberGenerator 为 protocol
    init(sides: Int, generator: RandomNumberGenerator) {
        self.sides = sides
        self.generator = generator
    }
    func roll() -> Int {
        return Int(generator.random() * Double(sides)) + 1
    }
}
```

# Delegation

Delegation 是一种 design pattern，即将一些功能委托给其他方法实现。其实现方式一般为：定义 protocols 封装需要委托的功能，保证遵循 protocols 的类型能提供这些功能。

# Adding Protocol Conformance with an Extension

通过 extension 可以使已有类型遵循 protocols。

```swift
protocol TextRepresentable {
    var textualDescription: String { get }
}

extension Dice: TextRepresentable { // 使已有类型遵循现有 protocols
    var textualDescription: String {
        return "A \(sides)-sided dice"
    }
}
```

## Conditionally Conforming to a Protocol

Genetics 可能只会在某些情况遵循某个 protocol，此时可以用 `where` 说明。

```swift
extension Array: someProtocol where Element: someProtocol {
    // 让 Array 类型只要在 Element 遵循 someProtocol 协议时就遵循 someProtocol 协议
}
```

## Declaring Protocol Adoption with an Extension

如果一个类型已经遵循了某个 protocol 中的所有要求，可以用 `extension` 让其直接遵循该 protocol，此时这个类型可以当作该 protocol 的类型使用。

```swift
struct Hamster {
    var name: String
       var textualDescription: String {
        return "A hamster named \(name)"
    }
}
extension Hamster: TextRepresentable {}
```

# Adopting a Protocol Using a Synthesized Implementation

Swift 可以在一些简单场景下自动合成 `Equatable`、`Hashable`、`Comparable` 的一些方法。

## Equatable

Swift 会为以下类型自动合成 `Equatable` 协议的实现：
- conform `Equatable` 协议且只有 Stored Properties 的 structures
- conform `Equatable` 协议且只有 associated types 的 enumerations
- 没有任何 associated types 的 enumerations

Swift 会自动为其合成 `==` 和 `!=`。

```swift
struct Vector3D: Equatable {
    var x = 0.0, y = 0.0, z = 0.0
}

let twoThreeFour = Vector3D(x: 2.0, y: 3.0, z: 4.0)
let anotherTwoThreeFour = Vector3D(x: 2.0, y: 3.0, z: 4.0)
if twoThreeFour == anotherTwoThreeFour {
    print("These two vectors are also equivalent.")
}
```

## Hashable

Swift 为以下几种自定义类型提供了 Hashable 协议的合成实现：
- conform `Hashable` 协议且只有 stored properties 的 structures
- conform `Hashable` 协议且只有 associated types 的 enumerations
- 没有任何 associated types 的 enumerations

Swift 会自动为其合成 `hash(into:)`。

## Comparable

Swift 为没有 raw values 的 enumerations 自动合成了 `Comparable` 实现（`<`、`<=`、`>`、`>=`）。如果 enumerations 里面有 associated types，则 associated types 也要遵循 `Comparable`。

```swift
enum SkillLevel: Comparable {
    case beginner
    case intermediate
    case expert(stars: Int)
}
var levels = [SkillLevel.intermediate, SkillLevel.beginner,
              SkillLevel.expert(stars: 5), SkillLevel.expert(stars: 3)]
for level in levels.sorted() {
    print(level)
}
```

# Collections of Protocol Types

Protocol Types 可以在 collections 中使用。

```swift
let things: [TextRepresentable] = [game, d12, simonTheHamster]

for thing in things {
    print(thing.textualDescription) // 只能访问 TextRepresentable 中定义的 properties 或 methods
}
```

# Protocol Inheritance

一个 protocol 可以继承其他的 protocols。

```swift
protocol InheritingProtocol: SomeProtocol, AnotherProtocol {
    // 这里是协议的定义部分
}
```

任何遵循 `InheritingProtocol` 的类型都要满足它的父协议。

# Class-Only Protocols

让 Protocols 继承 `AnyObject` 可以限制它只能被 classes（以及非 structures 和 enumerations 的类型）遵循。

```swift
protocol SomeClassOnlyProtocol: AnyObject, SomeInheritedProtocol {
    // 这里是 Class-Only Protocols 的定义部分
}
```

# Protocol Composition

将 protocols 当作 types 使用时，如果要求一个类型遵循多个协议，可以用 protocol composition，即 `SomeProtocol & AnotherProtocol`。

```swift
func wishHappyBirthday(to celebrator: Named & Aged) {
    print("Happy birthday, \(celebrator.name), you're \(celebrator.age)!")
}
```

# Checking for Protocol Conformance

检查类型是否遵循某个 protocol 也可以用 `is`、`as?`、`as!`。

```swift
for object in objects {
    if let obj = object as? HasArea {
        // ...
    } else {
        // ...
    }
}
```

# Optional Protocol Requirements

Protocols 可以定义 optional requirements，遵循该 protocols 的类型可以自己选择是否实现这些要求。

如果要和 objective-c 交互，那么要在 protocols 和 methods 前标注 `@obj`，其只能被 objective-c 的 classes 或者同样是 `@obj` 的 classes 继承，其他 classes 或者 structures 和 enumerations 都不能使用。

使用 optional requirements 时，其类型会自动变为 optional 类型，如 `(Int) -> String` 变成 `((Int) -> String)?`。

Optional requirements 可以通过 optional chaning 调用，即 `someOptionalMethod?(someArgument)`。

```swift
@objc protocol CounterDataSource {
    @objc optional func increment(forCount count: Int) -> Int
    @objc optional var fixedIncrement: Int { get }
}
```

# Protocol Extensions

通过对 protocols 使用 extension，可以为遵循该 protocols 的类型添加要求或者实现。

但是 extensions 不能声明该 protocol 继承自另一个 protocol。

```swift
extension RandomNumberGenerator {
    func randomBool() -> Bool {
        return random() > 0.5
    }
}
```

## Providing Default Implementations

可以通过 extension 为 protocols 内的 computed properties 和 methods 提供默认实现（如果有自定义实现，则使用自定义实现），只要在定义前用 `optional` 修饰。

```swift
extension PrettyTextRepresentable  { // 为 prettyTextualDescription 提供默认实现
    var prettyTextualDescription: String {
        return textualDescription
    }
}
```

## Adding Constraints to Protocol Extensions

扩展 protocols 时，可以指定额外的限制条件，只有符合条件的类型才能获得扩展。

用 `where` 添加条件。

```swift
extension Collection where Element: Equatable {
    func allEqual() -> Bool {
        for element in self {
            if element != self.first {
                return false
            }
        }
        return true
    }
}
```

# Metatype

类型本身可以看作一个对象，有 “获取占用空间大小” 等操作，类型的类型被称为 metaType。

用 `Type` property 可以获取 metaType，用 `self` 可以获取类型（对于表达式来说，`expr.self` 返回值。对于类型而言，`SomeClasses.self` 会返回本身）。

`Int.max == Int.self.max`，`AnyClasses == AnyObject.Type`。

```swift
let intMetatype: Int.Type = Int.self
```

## self

可以用 `.self` 或者 `type(of:)` 获取类型，区别在于 `.self` 返回静态类型，`type(of:)` 返回动态类型。

```swift
let myNum: Any = 1
type(of: myNum) // Int.type
myNum.self // Any
```

## Protocol

Protocols 并不是一个类型，因此不能用 `.Type`，应该用 `.Protocol`。

```swift
let protMetatype: MyProtocol.Protocol = MyProtocol.self
```
