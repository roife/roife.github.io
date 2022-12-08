---
layout: "post"
title: "「The Swift PL」 15 Deinitialization"
subtitle: "析构方法"
author: "roife"
date: 2020-09-15

tags: ["Swift 程序语言@读书笔记", "Swift@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Deinitialization

Deinitializers 用 `deinit` 标示，用于释放用户自己的资源（RAII）。

一个 Classes 只能有一个 Deinitializer，且不带参数和圆括号。

```swift
deinit {
    // 执行析构过程
}
```

Deinitializers 在资源被释放前调用，开发者不能主动调用 deinitializers。

子类继承了父类的 deinitializer，并且在子类的 deinitializer 最后，会自动调用父类的 deinitializer。即使子类没有自定义 deinitializer，也会自动调用父类的 deinitializer。
