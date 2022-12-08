---
layout: "post"
title: "「The Swift PL」 18 Type Casting"
subtitle: "类型转换"
author: "roife"
date: 2020-09-15

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Type Casting

类型转换可以用来判断实例的类型，或者检查类型是否遵从了某个 protocol。

# Defining a Class Hierarchy for Type Casting

在数组中存储同一父类的多个子类类型的数据，数组元素类型可以被推断为父类类型。
此时从数组中取出元素的类型为父类类型，需要通过类型转换将其转换为原来的类型。

```swift
class MediaItem {

}

class Movie: MediaItem {
}

class Song: MediaItem {
}

let library = [
    Movie(),
    Song(),
    Movie(),
]
// 数组 library 的类型被推断为 [MediaItem]
```

# Checking Type

用 `is` 检查某个实例是否属于特定类型。

```swift
var movieCount = 0
var songCount = 0

for item in library {
    if item is Movie {
        movieCount += 1
    } else if item is Song {
        songCount += 1
    }
}
```

# Downcasting

某种类型的常量可能实际上属于一个子类类型，此时可以用 `as?` 或 `as!` 转换。其中 `as?` 返回一个 Optional 类型，`as!` 则自动进行强制 decompose。

```swift
for item in library {
    if let movie = item as? Movie {
        print("Movie: \(movie.name), dir. \(movie.director)")
    } else if let song = item as? Song {
        print("Song: \(song.name), by \(song.artist)")
    }
}
```

# Type Casting for Any and AnyObject

- `Any` 可以表示任何类型，包括函数类型
- `AnyObject` 可以表示任何 Classes 类型的实例

```swift
var things = [Any]()

things.append(0)
things.append(0.0)
things.append("hello")
things.append((3.0, 5.0))
things.append(Movie(name: "Ghostbusters", director: "Ivan Reitman"))
things.append({ (name: String) -> String in "Hello, \(name)" })
```

可以用 `case` 语句

```swift
for thing in things {
    switch thing {
    case 0 as Int:
        // ...
    case 0 as Double:
        // ...
    case let someInt as Int:
        // ...
    case let someDouble as Double where someDouble > 0:
        // ...
    case is Double:
        // ...
    case let someString as String:
        // ...
    case let (x, y) as (Double, Double):
        // ...
    case let movie as Movie:
        // ...
    case let stringConverter as (String) -> String:
        // ...
    default:
        // ...
    }
}
```

注意：`Any` 可以表示 Optional 类型，将 Optional 作为 `Any` 使用时会发生警告，此时需要显式转换。

```swift
let optionalNumber: Int? = 3
things.append(optionalNumber)        // 警告
things.append(optionalNumber as Any) // 没有警告
```
