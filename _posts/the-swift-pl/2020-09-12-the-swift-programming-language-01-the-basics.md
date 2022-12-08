---
layout: "post"
title: "「The Swift PL」 01 The Basics"
subtitle: "Swift 基础语法"
author: "roife"
date: 2020-09-12

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Constants and Variables

## Declaration

- `let` 定义常量，`var` 定义变量

```swift
let maxNumber = 10
var curLoginAttempt = 0
```

## Type Annotations

```swift
var welcomeMessage: String

var red, green, blue: Double
```

# Comments

```swift
// This is a comment.

/* This is also a comment. */
```

# Semicolons

Swift 不强制要求加分号。

# Integers

Integers 包括 `UInt8`\`Int32`\`Int`\`UInt`（位数平台相关）等。

## Integer Bounds

```swift
let minValue = UInt8.min  // minValue is equal to 0, and is of type UInt8
let maxValue = UInt8.max  // maxValue is equal to 255, and is of type UInt8
```

# Floating-Point Numbers

Floating-Point Numbers 包括 `Double`（64 bit）和 `Float`（32 bit）。

# Type Safety and Type Inference

```swift
let meaningOfLife = 42 // 默认为 Int

let pi = 3.14159 // 默认为 Double
```

# Number Literals

Integer:
- 十进制：`17`
- 二进制：`0b1001`
- 八进制：`0o21`
- 十六进制：`0x11`

Floating-Point Numbers:
- 十进制 `* 10^exp`: `1.25e2` 即 `125.0`
- 十六进制 `* 2^exp`: `0xFp2` 即 `60.0`

二者都可以加数字分隔符（`_`）和前缀零：`00123.456`、`1_000_100`。

# Numeric Type Conversion

一般情况下，即使是非负数，也推荐用 `Int`。（为了匹配 Literals）

Swift 不允许溢出，也不允许隐式类型转换，需要用 `Type(Value)` 进行显式类型转换。

```swift
let cannotBeNegative: UInt8 = -1 // 报错

let one: Int = 1
let two: UInt8 = 2
let ans = one + two // 报错
let ans2 = UInt8(one) + two // 正确
```

Floating-Point Numbers 同样不能隐式转换为 Integers，且显式转换时总是会被截断（`3.9 => 3`，`-3.9 => -3`）。

但是 Literals 之间运算不用显式类型转换。

# Type Aliases

```swift
typealias AudioSample = UInt16
var maxAmplitudeFound = AudioSample.min
```

# Booleans

Swift 不允许其他类型向 Booleans 自动转换。

# Tuples

Tuples 可以是任意类型的组合。

Tuples 也可以被解压（Decompose），此时可以用 `_` 占位。

```swift
let http404Error = (404, "Not Found")
let (statusCode, statusMessage) = http404Error
let (justTheStatusCode, _) = http404Error
```

Tuples 也可以用 index 访问，或者用名字访问（前提是元素有名字）。

```swift
print("The status code is \(http404Error.0)")

let http200Status = (statusCode: 200, description: "OK")
print("The status code is \(http200Status.statusCode)")
```

# Optionals

Optional 类型的值有两种情况：有一个具体的值，或者没有值（`nil`）。

```swift
let possibleNumber = "123"
let convertedNumber = Int(possibleNumber) // 类型为 Int?，因为可能会转换失败
convertedNumber = nul // 表示无值
```

Optional 类型默认为 `nil`。

```swift
var surveyAnswer: String?
```

## If Statements and Forced Unwrapping

用 `!` 可以进行强制 Unwrapping。

```swift
if convertedNumber != nil {
    print("convertedNumber has an integer value of \(convertedNumber!).")
}
```

## Optional Binding

`if` 和 `while` 中可以用 `let` 或 `var` 进行检查和 Optional 绑定。

绑定可以重复。

- `Int(string)` 将 String 转换成 Int，返回 `Int?` 表示是否转换成功

```swift
if let actualNumber = Int(possibleNumber) {
    // ...
} else {
    // ...
}

if let firstNumber = Int("4"), let secondNumber = Int("42"), firstNumber < secondNumber && secondNumber < 100 {
    // ...
}
```

对于 Optional 类型，如果只是希望 unwrap，且后面不再需要原来的 Optional 变量，则可以用下面的简化写法：

```swift
if let myNumber {
    print("My number is \(muNumber)")
}
```

## Implicitly Unwrapping Optionals

当保证 Optionals 可以被安全 Unwrapping 时，可以用直接用 Implicitly Unwrapping Optionals（在类型后面加 `!`）来减少 `!` 的使用，此时 Optionals 可以像 non-Optionals 一样使用。

主要用在 class initialization。

```swift
var optionalString: String? = "optional"
var string: String = optionalString!

var definitelyString: String! = optionalString

print(optionalString!)
print(definitelyString)
```

# Error Handling

```swift
func canThrowAnError() throws {
    // this function may or may not throw an error
}

do {
    try canThrowAnError()
    // no error was thrown
} catch xxxError {
    // an error was thrown
}
```

# Assertions and Preconditions

用于运行时的错误检查。

## Assertions

```swift
let age = -3
assert(age >= 0, "A person's age can't be less than zero.")
```

`assertionFailure` 可以直接抛出断言（用于已经用 `if` 检查的情况）。

```swift
if age > 10 {
    // ...
} else if age >= 0 {
    // ...
} else {
    assertionFailure("A person's age can't be less than zero.")
}
```

## Preconditions

Preconditions 也有 `preconditions()` 和 `preconditionFailure`。

区别在于 Assertions 是 Debug 版本中检查，Preconditions 在 Debug 和 Product 版本中都会检查（因此会拖慢速度）。

如果编译时打开 `-Ounchecked` 则不会检查 Preconditions，但是仍然可以用 `fatalError` 强制抛错。

在不检查 Assertions 和 Preconditions 的情况下，编译器会默认他们正确，并且将其当作条件优化程序。
