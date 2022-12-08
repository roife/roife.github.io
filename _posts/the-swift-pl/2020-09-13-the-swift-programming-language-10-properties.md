---
layout: "post"
title: "「The Swift PL」 10 Properties"
subtitle: "属性"
author: "roife"
date: 2020-09-13

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Properties

Properties 分为 Stored properties 和 Computed properties。

Stored properties 和 Computed properties 都和实例关联，和类型关联的叫 Type properties。

# Stored Properties

Stored properties 可以是 `let` 也可以是 `var`。

```swift
struct FixedLengthRange {
    var firstValue: Int
    let length: Int
}

var rangeOfThreeItems = FixedLengthRange(firstValue: 0, length: 3)
rangeOfThreeItems.firstValue = 6
```

## Stored Properties of Constant Structure Instances

对于 Structures，如果实例定义为 `let`，那么即使是 `var` 的 properties 也是不可变的（因为 structures 是 Value Types）。但是 Class Type 可以修改。

## Lazy Stored Properties

Lazy Stored Properties 指第一次被调用时才会计算初始值的 properties，用 `lazy` 声明，必须用 `var` 声明。

```swift
class DataImporter {
    // DataImporter 初始化会消耗不少时间。
    // ...
}

class DataManager {
    lazy var importer = DataImporter()
    var data = [String]()
}

let manager = DataManager()
manager.data.append("Some data")
// importer 属性还没创建

print(manager.importer.fileName)
// importer 属性创建了
```

如果一个 `lazy` properties 在没有初始化完成时被多个线程访问，那么它可能会被初始化多次。

# Computed Properties

Computed Properties 不存储值，而是提供了 `getter` 和一个可选的 `setter` 返回值。

```swift
struct Point {
    var x = 0.0, y = 0.0
}
struct Size {
    var width = 0.0, height = 0.0
}
struct Rect {
    var origin = Point()
    var size = Size()
    var center: Point {
        get {
            let centerX = origin.x + (size.width / 2)
            let centerY = origin.y + (size.height / 2)
            return Point(x: centerX, y: centerY)
        }
        set(newCenter) {
            origin.x = newCenter.x - (size.width / 2)
            origin.y = newCenter.y - (size.height / 2)
        }
    }
}
var square = Rect(origin: Point(x: 0.0, y: 0.0),
    size: Size(width: 10.0, height: 10.0))

let initialSquareCenter = square.center

square.center = Point(x: 15.0, y: 15.0)
```

## Shorthand Setter Declaration

如果 `setter` 的参数没有定义参数名，则可以用 `newValue` 替代。

```swift
struct AlternativeRect {
    var origin = Point()
    var size = Size()
    var center: Point {
        get {
            let centerX = origin.x + (size.width / 2)
            let centerY = origin.y + (size.height / 2)
            return Point(x: centerX, y: centerY)
        }
        set {
            origin.x = newValue.x - (size.width / 2)
            origin.y = newValue.y - (size.height / 2)
        }
    }
}
```

## Shorthand Getter Declaration

如果 `getter` 是单一表达式，则可以隐式返回这个结果。

```swift
struct CompactRect {
    var origin = Point()
    var size = Size()
    var center: Point {
        get {
            Point(x: origin.x + (size.width / 2),
                  y: origin.y + (size.height / 2))
        }
        set {
            origin.x = newValue.x - (size.width / 2)
            origin.y = newValue.y - (size.height / 2)
        }
    }
}
```

## Read-Only Computed Properties

只有 `getter` 没有 `setter` 的 properties 是 Read-Only Computed Properties。

Computed Properties 必须用 `var` 声明，因为其值是不固定的。

Read-Only Computed Properties 可以省略 `get` 关键字和花括号。

```swift
struct Cuboid {
    var width = 0.0, height = 0.0, depth = 0.0
    var volume: Double {
        return width * height * depth
    }
}
```

# Property Observers

Property Observers 可以检测 properties 的变化，每次设置属性时都会调用。

可以在 3 个地方定义 Property Observers：
- 自定义的 Stored properties
- 继承的 Stored properties
- 继承的 Computed properties
- 对于自定义的 Computed properties，一般直接使用 `setter` 监测

可以设置的 observers 有两种
- `willSet` 设置前调用，传入常量新属性值，可以为参数指定一个名称（默认为 `newValue`）
- `didSet` 设置后调用，传入旧属性值，可以为参数指定一个名称（默认为 `oldValue`，当前参数仍然用当前变量名访问）
- `didSet` 中可以对 properties 进行赋值，且会覆盖掉已经赋的值，而 `willSet` 则不行

在父类初始化方法调用之后，在子类构造器中给父类的 properties 赋值时，会调用父类的 observers。而在父类初始化方法调用之前，给子类的 properties 赋值时不会调用子类的 observers。

将带有 observers 的参数作为 In-Out 参数传入函数时，也会调用 Observers，因为函数参数的传入和传出实际上进行了拷贝。

```swift
class StepCounter {
    var totalSteps: Int = 0 {
        willSet(newTotalSteps) {
            print("将 totalSteps 的值设置为 \(newTotalSteps)")
        }
        didSet {
            if totalSteps > oldValue  {
                print("增加了 \(totalSteps - oldValue) 步")
            }
        }
    }
}

let stepCounter = StepCounter()
stepCounter.totalSteps = 200
// 将 totalSteps 的值设置为 200
// 增加了 200 步

stepCounter.totalSteps = 360
// 将 totalSteps 的值设置为 360
// 增加了 160 步
```

# Property Wrappers

Property Wrappers 可以让一段代码在多个 properties 上面复用。

定义 Property Wrappers 需要首先定义一个包含 `wrappedValue` property 的 structure、enumeration 或 classes，然后用 `@propertyWrapper` 修饰。

使用 Property Wrappers 的 property 会从 `wrappedValue` 中读取和设置变量。

```swift
@propertyWrapper
struct TwelveOrLess {
    private var number: Int // 用 private 是为了更好地封装
    init() { self.number = 0 }
    var wrappedValue: Int {
        get { return number }
        set { number = min(newValue, 12) }
    }
}

struct SmallRectangle {
    @TwelveOrLess var height: Int
    @TwelveOrLess var width: Int
}

var rectangle = SmallRectangle()
print(rectangle.height) // 打印 "0"

rectangle.height = 24
print(rectangle.height) // 打印 "12"
```

```swift
/* 等价于这段代码 */
struct SmallRectangle {
    private var _height = TwelveOrLess()
    private var _width = TwelveOrLess()
    var height: Int {
        get { return _height.wrappedValue }
        set { _height.wrappedValue = newValue }
    }
    var width: Int {
        get { return _width.wrappedValue }
        set { _width.wrappedValue = newValue }
    }
}
```

## Setting Initial Values for Wrapped Properties

使用 Wrappers 的代码不能直接设置初始值，在 Wrappers 中可以添加 `init(wrappedValue:)` 方法来接受初始值。赋值会被自动当成参数 `wrappedValue` 的值传入。

```swift
@propertyWrapper
struct SmallNumber {
    private var maximum: Int
    private var number: Int

    var wrappedValue: Int {
        get { return number }
        set { number = min(newValue, maximum) }
    }

    init() {
        maximum = 12
        number = 0
    }
    init(wrappedValue: Int) {
        maximum = 12
        number = min(wrappedValue, maximum)
    }
    init(wrappedValue: Int, maximum: Int) {
        self.maximum = maximum
        number = min(wrappedValue, maximum)
    }
}

struct UnitRectangle { // 调用 init(wrappedValue:)
    @SmallNumber var height: Int = 1
}

struct NarrowRectangle { // 调用 init(wrappedValue:maximum:)
    @SmallNumber(wrappedValue: 2, maximum: 5) var height: Int
}

struct MixedRectangle {
    @SmallNumber(maximum: 9) var height: Int = 2
}
```

## Accessing a Property Wrapper

在 property 名字前面加上 `_` 相当于访问 Wrapper 的实例。

```swift
@propertyWrapper
struct Wrapper<T> {
    var wrappedValue: T

    func foo() { print("Foo") }
}

struct HasWrapper {
    @Wrapper var x = 0

    func foo() { _x.foo() }
}
```

## Projecting a Value From a Property Wrapper

Projected Value 用 `$` 开头，其余部分和 properties 同名，返回 propertyWrapper 中的 `projectedValue`。

Projected Value 的作用就是暴露一些 Wrapper 的接口

```swift
@propertyWrapper
struct Wrapper<T> {
    var wrappedValue: T

    var projectedValue: Wrapper<T> { return self }

    func foo() { print("Foo") }
}

struct HasWrapper {
    @Wrapper var x = 0

    func foo() { _x.foo() }
}

let a = HasWrapper()
a.$x.foo() // Prints 'Foo'
```

总结起来就是
- `x`: `wrappedValue`
- `_x`: `wrapper` itself
- `$x`: `projectionValue`

在定义中访问 Projected Value 可以不用加 `self`。

```swift
struct HasWrapper {
    @Wrapper var x = 0

    func foo() { $x.foo() }
}
```

# Global and Local Variables

Global Variables 默认都是 lazy-evaluate 的，而 Local Variables 默认都是立即计算。

Global Variables 也可以定义 Computed Variables 和对应的 Wrappers。

# Type Properties

Type Properties 是多个实例间共用的 properties，类似于 static 变量。

Stored Type Properties 必须要有初始值，而且是 lazy 的，即使被多线程访问也只会初始化一次。

## Type Property Syntax

```swift
struct SomeStructure {
    static var storedTypeProperty = "Some value."
    static var computedTypeProperty: Int {
        return 1
    }
}
```

```swift
enum SomeEnumeration {
    static var storedTypeProperty = "Some value."
    static var computedTypeProperty: Int {
        return 6
    }
}
```

在 Classes 中，对于 Computed Type Properties，可以用 `class` 替代 `static`，从而支持子类对父类的实现进行 Override。

```swift
class SomeClass {
    static var storedTypeProperty = "Some value."
    static var computedTypeProperty: Int {
        return 27
    }
    class var overrideableComputedTypeProperty: Int {
        return 107
    }
}
```

## Querying and Setting Type Properties

Type Properties 的访问通过类型进行，而不通过实例进行访问。

```swift
print(SomeStructure.storedTypeProperty)
SomeStructure.storedTypeProperty = "Another value."
```

和普通类型一样，Type Properties 也可以用 Observer、Wrapper 等。
