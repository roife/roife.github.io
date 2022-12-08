---
layout: "post"
title: "「Core Java」 02 Objects and Classes"
subtitle: "对象与类"
author: "roife"
date: 2021-01-25

tags: ["Java@编程语言", "Core Java@读书笔记", "读书笔记@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 类

Java 中的变量相当于一个指针，赋值时并没有拷贝对象，而是指向了一个对象（称为引用）。对象为 `null` 时表示没有引用任何对象。
复制一个对象需要调用 `clone()` 方法。

定义了对象变量不意味着定义了一个对象，必须用 `new` 来构造。（C++ 中则不需要）

```java
Date deadline;        // deadline doesn't refer to any object
s = deadline.toString();  // 非法
```

- mutator method：调用方法会改变自身属性
- accessor method：调用方法不改变自身属性，只访问对象（对应 C++ 的 `const` 方法）

# 多文件编译

比如两个文件 `a.java` 和 `aTest.java`，后者调用了前者，那么可以直接用 `javac aTest.java` 编译，编译器会自动寻找对应的 `class` 文件编译，如果没有，则寻找对应的 `java` 文件编译。甚至如果 `class` 文件版本比 `java` 旧，则会自动重新编译 `java`。

# 自定义类

```java
class ClassName {
  field1;
  field2;
  ...
  constructor1
  constructor2
  ...
  method1
  method2
}
```

Java 中所有的方法都必须在类内定义。

`this` 为方法的隐式参数（也是每个方法的第一个参数，但是不写出来）。

## 构造器

和 C++ 差不多，包括如果存在自定义 constructor，则不会合成默认的 constructor。

Java 中可以直接给某个变量赋值（或者调用方法）。

```java
class Employee {
    private String name = "";
}
```

### 构造器委托

可以直接用 `this` 调用另外一个构造器。

```java
public Employee(double s) {
    // calls Employee(String, double)
    this("Employee #" + nextld, s);
}
```

### 初始化块

初始化块在构造器之前运行。最好把初始化块放在变量定义之后。

```java
class Employee {
    private static int nextld;
    private int id;
    private String name;
    private double salary;

    // object initialization block
    {
        id = nextld;
        nextld++;
    }
    public Employee() {
        name = salary = 0;
    }
}
```

对于 `static` 成员，则应该使用 `static` 初始化块。

```java
static {
    // ...
}
```

### 初始化顺序

1. 默认初始化
2. 调用初始化语句和初始化块
3. 调用构造器

## 析构方法 `finalize`

可以使用 `finalize` 方法获得类似于析构方法的效果，在 GC 回收资源之前被调用。

## 封装

通常不会将一个变量定义为 `public`，而是：
- 变量定义为 `private`
- 定义一个 mutator method 来访问变量（直接返回）
- 定义一个 accessor method 来修改变量

mutator method 可以在修改前对值进行检查，accessor method 可以更灵活地调整返回值。

如果要返回一个可变对象，那么必须返回其拷贝，否则会导致对象被改变。

```java
class Employee {
    public Date getHireDay() {
        return (Date) hireDay.clone();
    }
}
```

方法可以访问该类型的任何一个私有属性，比如 `equals` 方法为了比较两个对象，必须访问所有数据（包括 `private`）。

## `final`

把变量设置为 `final` 可以让变量不再更改。但是对于引用类型，只是让其不指向其他对象，不能保证引用的对象不被修改。

# `static`

即静态变量（方法）。
- 静态变量通常公有常量会设置成静态，即 `public static final`
- 静态方法可以看成没有 `this` 的方法，只能访问自己的静态域，一般在三种情况下用
  + 方法与对象状态无关
  + 方法只访问静态域时使用
  + 用作静态工厂方法

访问 `static` 成员直接用 `.`，C++ 中则需要用 `::`。

## `main` 方法

每个类的 `main` 方法之所以设置成 `static`，是因为启动程序时还不存在对象，`main` 方法中可以创建当前类的对象（用于单元测试）。

```java
class Employee {
    public Employee() {
        // ...
    }
    public static void main(String[] args) {
        Employee e = new Employee();
        // 测试
    }
}
```

# 方法参数

Java 中方法参数默认为按值调用。

对于引用时传参会传递一个引用，但是这个和 C++ 里面的引用不同，相当于传递了一个指针。即方法可以改变对象状态，但是不能让改变引用的对象。

```java
public static void swap(Employee x, Employee y) { // doesn't work
    Employee temp = x;
    x = y;
    y = temp;
}

swap(a, b);
// x 和 y 的值确实被交换了，但是 a 和 b 的引用仍然不变
```

# 包

Java 可以用 package 组织代码。为了防止冲突，Sun 公司建议使用公司的互联网域名的逆序来命名包，如 `horstmann.com` 的 `corejava` 包变成 `com.horstmann.corejava`。注意嵌套的包之间没有关系，如 `a.b` 和 `a` 是两个不同的包。

package 比较类似于 `namespace`。

## 导入包

```java
java.tiie.LocalDate today = java.tine.Local Date.now() ;
// 或者
import java.time.LocalDate;
// 或者
import java.util.*; // 注意不能用 import java.util.*.*
```

如果导入的包有两个相同的类，则有可能发生冲突，此时可以重新导入特定类，或者在使用时指明类名。

```java
import java.util.*;
import java.sql.*;
import java.util.Date;
// 或者
java.util .Date deadline = new java.util .Date() ;
java.sql .Date today = new java.sql .Date();
```

## 静态导入

即 `using namespace xxx`。可以直接使用 `static` 方法，而不用加类名前缀。

```java
import static java.lang.Math
double z = sqrt(pow(x, 2) + pow(y, 2)) // Math.sqrt(Math.pow(x, 2) + Math.pow(y, 2))
```

## 将类放入包中

在源文件开头声明包，可以将类放入包中。

```java
package com.horstmann.corejava;
```

如果没有声明包，则放入默认包。包中文件需要放在对应的目录下（否则可以编译，但是不能运行）：

```
|- PackageTest.java
|- PackageTest.class
|- com/
    |- horstmann/
        |- corejava/
            |- Employee.java
            |- Employee.class
```

## 包作用域

如果一个变量不设置访问限制（`public` 等），则默认是包内可见的。这好吗？这不好。所以建议给变量都加上 `private`。

包是很容易被改变的，比如进入对应的目录并创建 `.java` 文件就可以更改包的内容并访问私有成员。因此 `java.` 开头的包都被禁止修改。如果要自己的包被禁止修改的话，可以用包密封 `package sealing` 技术。

# 类路径

```shell
java -classpath /home/user/classdir:.:/home/user/archives/archive.jar MyProg
```

或者直接写到环境变量 `CLASSPATH` 下。

# javadoc

javadoc 可以将代码中的注释提取出来生成文档，包括：
- 包
- `public` 类与接口
- `public/protected` 构造器及方法
- `public/protected` 域

其中注释要以 `/**` 开头，以 `*/` 结束。

注释由标记和自由格式文本组成。
- 标记：如 `@author` 或 `@param`
- 自由格式文本：第一句为概要。可以用 HTML 标记
  + 强调：`<em>...</em>`
  + 着重强调：`<strong>...</strong>`
  + 图像：`<img ...>`，用到的图像应该放到 `doc-files` 目录下
  + 代码：`{@code ...}`

## 类注释

紧跟在类定义之前。

```java
/**
 * A {©code Card} object represents a playing card, such
 * as "Queen of Hearts". A card has a suit (Diamond, Heart,
 * Spade or Club) and a value (1 = Ace, 2 . . . 10, 11 = Jack,
 * 12 = Queen, 13 = King)
 */
public class Card {

}

```

## 方法注释

- `@param`：变量描述
- `@return`：返回值描述
- `@throws`：异常描述

```java
/**
 * Raises the salary of an employee.
 * @param byPercent the percentage by which to raise the salary (e.g. 10 means 10%)
 * @return the amount of the raise
 */
public double raiseSalary(double byPercent) {
    double raise = salary * byPercent / 100;
    salary += raise;
    return raise;
}
```

## 域注释

只需要对公有域建立注释。

```java
/**
 * The "Hearts" card suit
 */
public static final int HEARTS = 1;
```

## 通用注释

- `@author`：作者
- `@version`：版本
- `@since`：引人某个特性的版本
- `@deprecated`：某个特性被废弃，如 `@deprecated Use <code> setVIsible(true) </code> instead`
- `@see`：为注释添加一个超链接，这些信息会被放在 `see also` 一栏
  + `@see com.horstraann.corejava.Employee#raiseSalary(double)`
  + `@see <a href="m«w.horstmann.com/corejava.htinl">The Core ]ava home page</a>`
  + `@see "Core Java 2 volume 2n`
- `@link`：插入链接，如 `{@link package.class#feature label}`

## 包注释

对于包，需要在包目录下提供单独的文件来写注释，有两种方法：
- `package.html`：内容写在 `<body>` 部分
- `package-info.java`：只有一个 `/** ... */` 的注释，不包含其他代码或注释

可以为所有源文件提供注释，放在父目录 `overview.html` 的 `<body>` 中。

## 提取注释

```shell
$ javadoc -d docDirectory nameOfPackage
```

用 `-author` 可以提取作者信息，其他类似。（不加则不会提取这些信息）

用 `-link` 可以为标准类添加超链接，如 `$ javadoc -link http://docs.oracle.eom/:javase/8/docs/api *.java`。

用 `-linksource` 可以将每个源文件转换成 HTML，每个类和方法名将转变为指向源代码的超链接。

# 类设计技巧

1. 一定要保证数据私有
2. 一定要对数据初始化
3. 不要在类中使用过多的基本类型（适当地用类封装）
4. 不是所有的域都需要独立的 mutator method 和 accessor method（final）
5. 将职责过多的类进行分解
6. 类名和方法名要能够体现它们的职责
7. 优先使用不可变的类
