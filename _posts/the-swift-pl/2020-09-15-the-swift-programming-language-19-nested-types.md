---
layout: "post"
title: "「The Swift PL」 19 Nested Types"
subtitle: "嵌套类型"
author: "roife"
date: 2020-09-15

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Nested Types

```swift
struct BlackjackCard {

    // ...
    enum Suit: Character {
        // ...
    }

    // ...
    enum Rank: Int {
        // ...
    }
    // ...
}
```

# Referring to Nested Types

在外部使用嵌套类型时，要在嵌套类型的类型名前加上其外部类型的类型名。

```swift
let heartsSymbol = BlackjackCard.Suit.hearts.rawValue
```
