---
layout: "post"
title: "「The Swift PL」 26 Access Control"
subtitle: "访问控制"
author: "roife"
date: 2020-09-22

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Modules and Source Files

为了方便起见，以下把所有能设置 access levels 的东西称为“实体”（entities）。

Modules 指独立的代码单元，如框架和 app，可以用 `import` 导入。

Swift 中，Xcode 的每个 target 都被当作独立的 modules。

Source Files 则是 modules 的组成部分。

# Access Levels

Swift 中有五种 access levels：
- `open` 和 `public` 可以让 entities 被同一 module 源文件中的所有其他 entities 访问，在 modules 外也可以通过导入这个 modules 来访问其所有 entities。二者通常用于指定框架的外部接口
- `internal` 让 entities 被同 module 源文件内的任何 entities 访问，但是不能在 modules 以外访问。通常用来定义内部接口
- `fileprivate` 限制 entities 只能在定义的文件内部访问
- `private` 限制 entities 只能在当前作用域或者同一文件的 `extension` 内访问

`open` 限制最少，`private` 限制最多。

`open` 只能用于 classes 和 classes 的 members，和 `public` 的区别在于 `open` 限定的 classes 或 members 能在 modules 外进行继承和 override。

## Guiding Principle of Access Levels

Entities 不能定义在 access levels 更严格的 entities 中。如 `public` 变量中不能定义 `internal` 的成员，函数的 access levels 也不能高于其参数类型和返回类型。

注意，类型本身有 access levels。

## Default Access Levels

Access levels 默认为 `internal`。

## Access Levels for Single-Target Apps

编写 single-target 的 apps 时，不考虑将其作为 modules 给其他人使用，则只要用 `internal`、`fileprivate` 和 `private` 即可。

## Access Levels for Frameworks

定义框架时，其对外的接口应当定义为 `open` 或 `public`。

## Access Levels for Unit Test Targets

默认情况下，Unit Test Targets 只能访问 `open` 和 `public` 接口，但是可以在导入应用程序 modules 前使用 `@testable` 修饰，并且开启编译选项 `Build Options -> Enable Testability`，此时可以访问应用程序 modules 内所有 `internal` 级别的 entities。

# Access Control Syntax

```swift
public class SomePublicClass {}
public var somePublicVariable = 0
internal let someInternalConstant = 0
fileprivate func someFilePrivateFunction() {}

class SomeInternalClass {}   // 隐式 internal
var someInternalConstant = 0 // 隐式 internal
```

# Custom Types

一个类型的 access levels 会影响其 members 的 default access levels。如 `private` 类型的 members 默认为 `private`。但是 `public` 类型的 members 依然默认为 `internal`（`public` 接口需要显式指定）。

```swift
public class SomePublicClass {                  // 显式 public 类
    public var somePublicProperty = 0            // 显式 public 类成员
    var someInternalProperty = 0                 // 隐式 internal 类成员
    fileprivate func someFilePrivateMethod() {}  // 显式 fileprivate 类成员
    private func somePrivateMethod() {}          // 显式 private 类成员
}
```

## Tuple Types

Tuples 的 access levels 不能单独指定，由其中最严格的类型决定。

如 `(internal, private)` 的 access levels 为 `private`。

## Function Types

函数的 access levels 由最严格的参数类型和返回类型决定。并且如果结果和当前环境默认的 access level 不同，那么需要显式指定其 access levels。

```swift
func someFunction() -> (SomeInternalClass, SomePrivateClass) {
    // 推断结果为 private，需要对函数进行显式的 access level 指定
}
```

## Enumeration Types

不能单独指定 enumerations 成员的访问级别，其级别和该 enumeration types 相同。

```swift
public enum CompassPoint {
    case north // access levels 都是 public
    case south
    case east
    case west
}
```

### Raw Values and Associated Values

Enumerations 内定义的 raw values 或者 associated values 的 access levels 不能低于该 enumeration types。如在 `interal` 中不能定义 `private` 的 raw value types。

# Subclasses

Subclasses 可以继承同一 modules 内可以访问的 classes，或者不同 modules 中用 `open` 修饰的 classes。子类的访问级别不能高于父类。

对于同一 modules，可以 override 所有可以访问的成员；对于不同 modules，可以 override 被 `open` 修饰的成员。

可以在子类中通过 override 给予成员更高的 access levels。

```swift
public class A {
    fileprivate func someMethod() {}
}

internal class B: A {
    override internal func someMethod() {}
}
```

在 access levels 允许下，子类高级别类型可以访问低级别类型。如 `interal` 可以访问 `fileprivate`。

# Constants, Variables, Properties, and Subscripts

常量、变量、properties、subscripts 同样不能拥有比所在类型更低的 access levels。

其中，subscripts 不能拥有比 index type 更低的 access levels。

## Getter and Setter

Getter 和 Setter 的 access levels 和所属类型相同。

对于 computed properties，Setter 的 access levels 可以低于 Getter，这样可以控制其读写权限。对于 stored properties 也可以进行相同的操作，只要用 `accessLevel(set)` 修饰。

```swift
public struct TrackedString {
    public private(set) var numberOfEdits = 0  // 指定能内部进行写操作
    public var value: String = "" {
        didSet {
            numberOfEdits += 1
        }
    }
    public init() {}
}
```

# Initializers

自定义 initializers 的 access levels 可以低于（更不严格）或者等于所属类型。唯一的例外是 required initializers 的 access levels 必须和所属类型相同。

同样，initializers 的 access levels 也不能低于参数的 access levels。

## Default Initializers

Default Initializers 的 access level 和所属类型相同。但是 `public` 类型的 default initializers 默认还是 `internal`。

## Default Memberwise Initializers for Structure Types

如果 structures 内任何 stored properties 的 access levels 都是 `private`，那么 default memberwise initializers 的 access level 就是 `private`，否则默认为 `internal`。

对于一个 `public` 的 structures，如果想要其 default memberwise initializers 在其他 modules 中访问，则需要手动定义一个 `public` 的 default memberwise initializers。

# Protocols

Protocols 也可以指定 access levels，限制其只在适当的范围内被遵循。Protocols 中的所有 methods 和 properties 默认和该 protocols 具有相同的 access levels（即使是 `public` 的 protocols，其内部成员也是 `public`），并且**不能自定义设置**。

## Protocol Inheritance

如果一个 protocol 继承了其他 protocols，则它的 access levels 必须低于被继承的 protocols。如继承自 `internal` 的 protocol 不能定义为 `public`。

## Protocol Conformance

一个类型可以继承低级别的 protocols，如 `public` 类型可以遵循一个 `internal` protocols，但是它只能在 `internal` protocol 所在的 modules 中使用。

遵循 protocols 时，类型所处的上下文必须是类型和 protocols 中最小的那一个。如一个 `public` 的类型，遵循一个 `internal` 的 protocols，则类型对该协议的遵循也是 `internal` 的。

编写或者扩展一个类型使其遵循一个 protocols 时，必须确保该类型对 protocols 要求的实现，至少和其一致。如 `public` 类型遵循 `internal` protocols，则这个类型对 protocols 的所有实现至少是 `internal` 的。

# Extension

Extension 中新增的成员具有和原始类型相同的 access levels。如 `public` 类型的 extension 默认为 `internal`，而 `fileprivate` 依然为 `fileprivate`。或者可以为 extension 指定默认 access levels，对 extension 内所有成员生效。

用 extension 遵循 protocols 时不能显式指定 access levels，必须遵循 protocols 的要求。

## Private Members in Extensions

扩展同一文件的 classes、structures、enumerations 时，表现和在原始类型中相同。

- 在类型的声明里声明一个 `private` 成员，可以在同一文件的 extension 里访问
- 在 extension 里声明一个 `private` 成员，在同一文件的另一个 extension 里访问
- 在 extension 里声明一个 `private` 成员，在同一文件的类型声明里访问

```swift
protocol SomeProtocol {
    func doSomething()
}

struct SomeStruct {
    private var privateVariable = 12
}

extension SomeStruct: SomeProtocol {
    func doSomething() {
        print(privateVariable)
    }
}
```

# Generics

泛型类型或者泛型函数的 access levels 取决于泛型类型或者函数本身，同时考虑类型参数和约束，取其中最低者。

# Type Alias

不同的 type alias 会被当作不同的类型（因此也可以拥有不同的 access levels），且其 access levels 不能高于表示的类型。

如 `public` 类型的 alias 可以是 `public`, `private` 等；但是 `private` 类型的 alias 不能是 `public` 的。
