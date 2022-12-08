---
layout: "post"
title: "「The Swift PL」 04 Collection Types"
subtitle: "集合类型"
author: "roife"
date: 2020-09-12

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Mutability of Collections

用 `var` 定义的集合类型是可变的，用 `let` 定义的类型内部是不可变的。

# Arrays

## Array Type Shorthand Syntax

数组可以写作 `Array<Element>` 或 `[Element]`。

## Creating an Empty Array

```swift
var someInts = [Int]()

someInts.append(3)
someInts = [] // 仍然为 [Int]
```

## Creating an Array with a Default Value

```swift
var threeDoubles = Array(repeating: 0.0, count: 3)
// threeDoubles is of type [Double], and equals [0.0, 0.0, 0.0]

var shoppingList: [String] = ["Eggs", "Milk"]
var shoppingList2 = ["Eggs", "Milk"]
```

## Creating an Array by Adding Two Arrays Together

```swift
var anotherThreeDoubles = Array(repeating: 2.5, count: 3)
// anotherThreeDoubles is of type [Double], and equals [2.5, 2.5, 2.5]

var sixDoubles = threeDoubles + anotherThreeDoubles
// sixDoubles is inferred as [Double], and equals [0.0, 0.0, 0.0, 2.5, 2.5, 2.5]
```

## Accessing and Modifying an Array

- `arr.count`：返回数组的数量
- `arr.isEmpty`：返回数组是否为空
- `arr.append(_:)`：添加数据（也可以用 `arr += [data]`）

数组下标索引从 `0` 开始。

用下标可以一次性改变一个范围（允许改变前后数组的数量不相同）。

```swift
shoppingList[0] = "Six eggs"
shoppingList[4...6] = ["Bananas", "Apples"]
```

数组同样可以用 `insert(_:at:)` 和 `remove(at:)` 增加或删除元素。

## Iterating Over an Array

```swift
for item in shoppingList {
    print(item)
}

for (index, value) in shoppingList.enumerated() {
    print("Item \(String(index + 1)): \(value)")
}
```

# Set

存储在集合中的类型必须是 hashable 的，自定义类型必须遵循 `Hashable Protocol` 和 `Equatable Protocol`。

## Set Type Syntax

Set 必须写成 `Set<Element` 初始化。

集合类型可以通过 Array Literal 创建，此时 `Set` 必须显式声明，但是元素类型可以被推断出来。

```swift
var favoriteGenres: Set = ["Rock", "Classical", "Hip hop"]
```

## Accessing and Modifying a Set

Set 同样有类似于 Array 的方法。

- `set.contains(_:)`：是否包含特定的值

## Iterating Over a Set

```swift
for genre in favoriteGenres {
    print("\(genre)")
}

for genre in favoriteGenres.sorted() { // 有序遍历
    print("\(genre)")
}
```

# Performing Set Operations

- `intersection(_:)`：交集
- `symmetricDifference(_:)`：不存在于两个集合中的元素
- `union(_:)`：并集
- `subtracting(_:)`：差集

```swift
let oddDigits: Set = [1, 3, 5, 7, 9]
let evenDigits: Set = [0, 2, 4, 6, 8]
let singleDigitPrimeNumbers: Set = [2, 3, 5, 7]

oddDigits.union(evenDigits).sorted()
// [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
oddDigits.intersection(evenDigits).sorted()
// []
oddDigits.subtracting(singleDigitPrimeNumbers).sorted()
// [1, 9]
oddDigits.symmetricDifference(singleDigitPrimeNumbers).sorted()
// [1, 2, 9]
```

- `==`：判断集合是否相等
- `isSubset(of:)`, `isSuperset(of:)`：包含关系
- `isStrictSubset(of:)`, `isStrictSuperset(of:)`：真子集关系
- `isDisjoint(with:)`：是否相交

```swift
let houseAnimals: Set = ["🐶", "🐱"]
let farmAnimals: Set = ["🐮", "🐔", "🐑", "🐶", "🐱"]
let cityAnimals: Set = ["🐦", "🐭"]

houseAnimals.isSubset(of: farmAnimals)
// true
farmAnimals.isSuperset(of: houseAnimals)
// true
farmAnimals.isDisjoint(with: cityAnimals)
// true
```

# Dictionary

Dictionary 可以用 `Disctionary<Key, Value>` 定义，也可以用 `[Key: Value]` 定义。

## Creating an Empty Dictionary

```swift
var namesOfIntegers = [Int: String]()
// namesOfIntegers 是一个空的 [Int: String] 字典

namesOfIntegers[16] = "sixteen"
namesOfIntegers = [:] // [Int: String]
```

## Creating a Dictionary with a Dictionary Literal

```swift
var airports: [String: String] = ["YYZ": "Toronto Pearson", "DUB": "Dublin"]
var airports2 = ["YYZ": "Toronto Pearson", "DUB": "Dublin"]
```

## Accessing and Modifying a Dictionary

Dictionary 同样也有 `count`，`isEmpty` 等 property。

可以用下标语法给 Dictionary 添加新值，或者改变已有的值。

```swift
airports["LHR"] = "London"
```

- `dict.updateValue(_:forKey:)`：更新对应的值，返回原值的 Optional 类型，可以检查是否更新成功

用下标获取字典内的值，其返回类型也是 Optional

```swift
if let airportName = airports["DUB"] {
    print("The name of the airport is \(airportName).")
} else {
    print("That airport is not in the airports dictionary.")
}
```

将字典的值赋值为 nil 可以移除它。

```swift
airports["APL"] = "Apple Internation"
airports["APL"] = nil
```

- `dict.removeValue(forKey:)`: 移除对应的值，返回原值的 Optional 类型，可以检查是否移除成功

## Iterating Over a Dictionary

```swift
for (airportCode, airportName) in airports {
    print("\(airportCode): \(airportName)")
}
```

用 `disct.keys` 或 `dict.values` 可以遍历 key 和值，甚至可以直接创建新数组。

```swift
for airportCode in airports.keys {
    print("Airport code: \(airportCode)")
}

for airportName in airports.values {
    print("Airport name: \(airportName)")
}

let airportCodes = [String](airports.keys)
let airportNames = [String](airports.values)
// 为了有序可以调用 sorted() 方法
```
