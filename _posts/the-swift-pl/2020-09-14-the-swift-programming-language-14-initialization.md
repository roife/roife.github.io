---
layout: "post"
title: "「The Swift PL」 14 Initialization"
subtitle: "构造方法"
author: "roife"
date: 2020-09-14

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Setting Initial Values for Stored Properties

实例化时必须为所有 Stored Properties 设置初始值。
为 Stored Properties 设置默认值或者在 `init` 里面设置初始值时，不会触发 property observers。

## Initializers

```swift
struct someStructures {
    init() {
        // ...
    }
}
```

## Default Property Values

设置 Default Property Values 比在 initializers 里面赋值更好。

```swift
struct Fahrenheit {
    var temperature = 32.0
}
```

# Customizing Initialization

## Initialization Parameters

```swift
struct Celsius {
    // ...
    init(fromFahrenheit fahrenheit: Double) {
        // ...
    }
}

let boilingPointOfWater = Celsius(fromFahrenheit: 212.0)
```

## Parameter Names and Argument Labels

Initializers 没有方法名，因此需要通过 argument labels 来区分调用的方法。
即使没有提供 argument labels，Swift 会使用 parameter names。

```swift
let veryGreen = Color(0.0, 1.0, 0.0) // 错误，没有提供 argument labels
```

## Initializer Parameters Without Argument Labels

用 `_` 可以省略 Argument Labels。

```swift
struct Celsius {
    // ...
    init(_ celsius: Double){
        // ...
    }
}

let bodyTemperature = Celsius(37.0)
```

## Optional Property Types

Optional Property Types 可以自动被初始化为 `nil`。

```swift
class SurveyQuestion {
    var text: String
    var response: String? // 自动为 nil
    init(text: String) {
        self.text = text
    }
}

```

## Assigning Constant Properties During Initialization

可以在 initializers 中给常量 properties 赋值。

常量 properties 只能在当前的 initializers 中修改，不能在子类的 initializers 中修改。

```swift
class SurveyQuestion {
    let text: String
    init(text: String) {
        self.text = text
    }
}
```

# Default Initializers

如果所有 properties 都有默认值，而且没有自定义 initializers，那么 Swift 会合成 Default Initializers。

```swift
class ShoppingListItem {
    var name: String? // 默认为 nil
    var quantity = 1
    var purchased = false
}
```

## Memberwise Initializers for Structure Types

如果 structure 没有任何自定义 initializers，那么将会合成 memberwise initializers（不要求 stored properties 有默认值）。

Memberwise initializers 用于逐一初始化成员，调用时可以省略具有默认值的 properties。

```swift
struct Size {
    var width = 0.0, height = 0.0
}
let twoByTwo = Size(width: 2.0, height: 2.0)
let zeroByTwo = Size(height: 2.0)
```

# Initializer Delegation for Value Types

Initializer Delegation 即调用其它 initializers 进行构造。Value types（structures 和 enumerations）的构造不包括继承，因此 delegation 比较简单。

对于 Value Types，可以用 `self.init()` 调用其他 initializers。

如果自定义了 initializers，那么就不再合成 defaulted initializers 和 memberwise initializers（但是可以把自定义 initializers 写在 `extension` 中）。

```swift
struct Rect {
    // ...
    init() {}

    init(origin: Point, size: Size) {
        // ...
    }

    init(center: Point, size: Size) {
        // ...
        self.init(origin: Point(x: originX, y: originY), size: size)
    }
}
```

# Class Inheritance and Initialization

Classes 中的所有 properties 都必须在构造的过程中设定初始值。

## Designated Initializers and Convenience Initializers

Designated Initializers 将初始化 Classes 的所有 properties，并调用父类的 initializers 不断进行构造。一个 Class 一般只有一个 Designated Initializer。

Convenience Initializers 一般用于辅助，可以用来调用 Designated Initializer，并为一些形参提供默认值，或者用来创建特殊的实例。

## Syntax for Designated and Convenience Initializers

```swift
init(parameters) {
    statements
}
```

Convenience Initializers 要在 `init` 前加上 `convenience` 关键字。

```swift
convenience init(parameters) {
    statements
}
```

## Initializer Delegation for Class Types

Classes 之间的 delegation 要遵从三条规则：
- Designated Initializers 必须调用直接父类的 Designated Initializers
- Convenience Initializers 必须调用当前类的其他 Initializers
- Convenience Initializers 必须在最后调用 Designated Initializers

即，Designated Initializers 总是向上调用，Convenience Initializers 总是横向调用。

## Two-Phase Initialization

Swift 中 Classes 的构造分为两个阶段：
1. 每一个 Stored properties 赋初始值
2. 自定义 Stored properties

Two-Phase 的构造过程使得构造过程更加安全和灵活，只有第一阶段完成后，实例才是有效的。

Swift 编译器还会进行四种安全检查：
1. Designated Initializers 必须保证当前 Class 的 properties 都完成初始化，然后才能调用父类的 initializers
2. Designated Initializers 必须在调用了父类的 initializers 后，再为继承的 properties 设置新值（否则会被父类的 initializers 覆盖）
3. Convenience Initializers 必须先调用其他 initializers，然后为其他 properties 赋新值
4. Initializers 的第一阶段完成之前不能调用任何实例 methods 或者读取实例 properties 的值，也不能引用 `self` 作为值

### Phase 1
1. 调用某个 Designated 或 Convenience Initializer
2. 完成内存分配（但是内存没有初始化）
3. Designated Initializer 确保当前 Class 的所有 Stored Properties 都已初始化
4. 当前的 Designated Initializer 执行父类的 Designated Initializer，设置父类的 properties
5. 沿着继承链不断向上执行
6. 达到继承链顶端，所有 properties 已经初始化完成

### Phase 2
1. 从继承链顶部向下，每个类的 Designated Initializer 有机会进一步自定义值，此时可以访问 `self`，修改 properties，调用实例 methods
2. Convenience Initializer 可以自定义和使用 `self`

## Initializer Inheritance and Overriding

Swift 中的子类默认不会继承父类的构造器。

在编写和父类中的相同的 Designated Initializer 时，实际上在重载，所以要加上 `override`（即使是合成的 initializer）。即使是在编写父类的 Convenience Initializer，只要和父类的 Designated Initializer 相同就要用 `override` 修饰。

编写 Convenience Initializer 时，由于子类不能调用父类的 Convenience Initializer，所以不需要 `override`。

```swift
class Vehicle {
    var numberOfWheels = 0
}

class Bicycle: Vehicle {
    override init() {
        super.init()
        numberOfWheels = 2
    }
}
```

如果子类的构造器在 Phase 2 没有自定义操作，那么可以省略 `super.init()` 的调用。

```swift
class Hoverboard: Vehicle {
    var color: String
    init(color: String) {
        self.color = color
        // super.init() 在这里被隐式调用
    }
}
```

子类可以在构造过程修改继承来的变量 property，但是不能修改继承来的常量 property。

## Automatic Initializer Inheritance

如果子类引入的所有新 properties 都提供了默认值，那么可以用以下规则自动继承 initializers：
1. 如果子类没有定义任何 Designated Initializer，则自动继承父类所有的 Initializers
2. 如果子类拥有（重写）所有父类 Designated Initializer（包括手动实现，改用 `convenience` 重写和按照规则 1 继承），则自动继承父类所有的 Convenience Initializer
3. 即使自定义了 Convenience Initializer，以上两个规则依然适用

# Failable Initializers

Failable Initializers 可以表达构造失败的情况。Failable Initializers 可以通过 `return nil` 表达构造失败的情况。

```swift
struct Animal {
    let species: String
    init?(species: String) {
        if species.isEmpty {
            return nil
        }
        self.species = species
    }
}
```

## Failable Initializers for Enumerations

```swift
enum TemperatureUnit {
    case Kelvin, Celsius, Fahrenheit
    init?(symbol: Character) {
        switch symbol {
        case "K":
            self = .Kelvin
        case "C":
            self = .Celsius
        case "F":
            self = .Fahrenheit
        default:
            return nil
        }
    }
}

let fahrenheitUnit = TemperatureUnit(symbol: "F")
if fahrenheitUnit != nil {
    print("This is a defined temperature unit, so initialization succeeded.")
}

```

## Failable Initializers for Enumerations with Raw Values

拥有 Raw Values 的 Enumerations 会自动合成 Failable Initializer `init?(rawValue:)`。

```swift
enum TemperatureUnit: Character {
    case Kelvin = "K", Celsius = "C", Fahrenheit = "F"
}

let fahrenheitUnit = TemperatureUnit(rawValue: "F")
if fahrenheitUnit != nil {
    print("This is a defined temperature unit, so initialization succeeded.")
}
```

## Propagation of Initialization Failure

Classes、Structures、Enumerations 的 Failable Initializers 可以横向 delegate 到自己的 Failable Initializers。

子类的 Failable Initializers 也可以 delegate 到父类的 Failable Initializers。

```swift
class Product {
    let name: String
    init?(name: String) {
        if name.isEmpty { return nil }
        self.name = name
    }
}

class CartItem: Product {
    let quantity: Int
    init?(name: String, quantity: Int) {
        if quantity < 1 { return nil }
        self.quantity = quantity
        super.init(name: name)
    }
}

// 此时 quantity < 1 或者 name.isEmpty 时都会构造失败
```

## Overriding a Failable Initializer

子类可以 override 父类的 failable initializers（可以用 failable initializer 覆盖，也可以用非 failable initializer 覆盖）。此时需要对父类的 failable initializer 进行强制 decompose。

可以用非 failable initializer 重写 failable initializer，但是不能反过来。

```swift
class Document {
    var name: String?

    init() {}
    init?(name: String) {
        if name.isEmpty { return nil }
        self.name = name
    }
}

class AutomaticallyNamedDocument: Document {
    override init() {
        super.init()
        self.name = "[Untitled]"
    }
    override init(name: String) {
        super.init()
        if name.isEmpty {
            self.name = "[Untitled]"
        } else {
            self.name = name
        }
    }
}
```

也可以在子类的非 failable initializers 上用强制 decompose 调用父类的 failable initializers（否则不能调用 failable initializers）。

```swift
class UntitledDocument: Document {
    override init() {
        super.init(name: "[Untitled]")!
    }
}
```

## The init! Failable Initializer

可以用 `init!` 定义一个 failable initializer，其返回值会被强制 decompose。

可以把 `init?` delegate 到 `init!`，或者用 `init?` override `init!`。（反过来也都可以）

可以把 `init` delegate 到 `init!`，但是构造失败时会出发 assertions。

# Required Initializers

在 initializers 前添加 `required` 表示所有子类必须 `override` 该 initializer。

```swift
class SomeClass {
    required init() {
        // 构造器的实现代码
    }
}
```

此时子类的 initializer 也要添加 `required` 修饰。

在重写父类的 required designated initializer 时，不需要加 `override` 修饰。

如果自动继承的 initializer 能满足 required initializer 的需求，则不需要显式提供 required initializer 的实现。

```swift
class SomeSubclass: SomeClass {
    required init() {
        // 构造器的实现代码
    }
}
```

# Setting a Default Property Value with a Closure or Function

```swift
class SomeClass {
    let someProperty: SomeType = {
        // someValue 必须和 SomeType 类型相同
        return someValue
    }()
}
```

用 closure 初始化 properties 注意实例的其他部分还没有初始化，因此不能访问。也不能用 `self` 调用实例方法。
