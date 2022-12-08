---
layout: "post"
title: "「The Swift PL」 16 Optional Chaining"
subtitle: "可选链"
author: "roife"
date: 2020-09-15

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Optional Chaining

Optional Chaining 就是在 Optional 类型上调用 properties、methods、subscripts。如果 Optional 为 `nil`，则返回 `nil`，否则返回值。

# Optional Chaining as an Alternative to Forced Unwrapping

在调用的 properties、methods、subscripts 后面加上 `?`，就定义了一个 Optional Chaining。这和 `!` 相似，但是 `!` 若遇到 `nil` 则会发生错误，而 Optional Chaining 只会调用失败。

无论 properties、methods、subscripts 本身是否为 Optional 类型，都可以用 `?`，且返回值都被包装成 Optional 类型。

```swift
class Person {
    var residence: Residence?
}

class Residence {
    var numberOfRooms = 1
}

let john = Person()
let roomCount = john.residence!.numberOfRooms // 强制 decompose 发生错误
if let roomCount = john.residence?.numberOfRooms {
    // ...
} else {
    // ...
}
```

- 调用 properties：`john.residence?.address`
- 调用 methods：`john.residence?.printNumberOfRooms()`
- 调用 subscripts：`firstRoomName = john.residence?[0].name`，`testScores["Bev"]?[0] += 1`（Dictionary）

# Linking Multiple Levels of Chaining

多层 Optional Chaining 的嵌套不会增加 Optional 类型的层级，如 `Int?` 用 Optional Chaining 调用后还是 `Int?`，不会变为 `Int??`。

```swift
if let johnsStreet = john.residence?.address?.street {
    // ...
} else {
    // ...
}
```

```swift
if let beginsWithThe =
    john.residence?.address?.buildingIdentifier()?.hasPrefix("The") {
        // ...
}
```

注意在方法上使用时不能丢掉 `()`，因为是在返回值上调用 Optional Chaining。
