---
layout: "post"
title: "「Core Java」 04 Interfaces & Lambda"
subtitle: "接口，lambda 表达式，内部类和 Proxy"
author: "roife"
date: 2021-01-28

tags: ["Java@编程语言", "Core Java@读书笔记", "读书笔记@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 接口

## interface 简介

Java 中的 interface 有点像 Swift 的 protocol 或者 C++ 的纯虚基类，用 `interface` 声明，其中的方法默认是 `public` 的（所以不需要访问控制符）。

```java
public interface Comparable<T> {
    int compareTo(T other);
}
```

声明实现某个 interface 用 `implements`。

```java
class Employee implements Comparable<Employee> {
    public int compareTo(Employee other) {
        return Double.compare(salary, other.salary);
    }
}
```

- `java.util.Arrays`
  + `static void sort(Object[] a)`：使用 mergesort 算法对数组 `a` 中的元素进行排序。要求数组中的元素必须属于实现了 `Comparable` 接口的类，并且元素之间必须是可比较的。

## `compareTo(x)`

语言规定 `compareTo(x)` 必须保证反对称性，即 `sgn(x.compareTo(y)) = -sgn(y.compareTo(x))`。基于这个原因，比较时不能进行简单的类型转换：

```java
class Employee implements Comparable<Employee> {
    // ..
}

class Manager extends Employee {
    public int compareTo(Employee other) {
        Manager otherManager = (Manager) other; // NO
    }
}
```

如果这么写，那么 `e.compareTo(m)` 正常，但是 `m.compareTo(e)` 会抛出 `ClassCastException` 异常，这就不符合反对称性，所以要求 `compareTo()` 方法在一开始先检测两个类是否相同，不同则直接抛出 `ClassCastException`。

```java
if (getClass() != other.getClass()) throw new ClassCastException();
```

但是如果要求允许继承关系的类之间比较，那么应该只在父类上提供 `compareTo()`，并且将其设置为 `final`。

## interface 的特性

- 不能用 `new` 创建 interface 的对象，但是能创建 interface 的引用，表示指向的对象实现了这个 interface

```java
x = new Comparable(); // Error
Comparable x; // OK
```

- interface 也可以用 `instanceof` 检查：`if (anObject instanceof Comparable)`

- interface 也可以存在继承之类的关系，用来扩展 interface

```java
public interface Powered extends Moveable {
    // ...
}
```

- interface 中可以包含常量。在其中定义域默认为 `public static final`

- 每个类只能够拥有一个超类，但却可以实现多个 interface（因此只能继承一个抽象类，但是能实现多个 interface）

```java
class Employee implements Comparable, Comparable
```

- Java SE8 开始允许静态方法，这样就不需要专门写一个静态方法的伴随类了（比如 `Collection/Collections`）

## 默认方法

可以为方法提供一个默认实现，用 `default` 修饰。

```java
public interface Comparable<T> {
    default int compareTo(T other) { return 0; } // By default, all elements are the same
}
```

默认方法有两个用处：
- 只关心某些特殊方法，而不实现所有方法
- 接口演化。假设为旧 interface 添加了一个新方法，默认方法可以让人不花时间去为旧代码提供新方法的实现，只要执行默认方法即可

### 默认方法冲突

如果父类实现了默认方法，那么会执行父类的默认方法（子类也默认执行父类方法，即类优先）。

如果两个 interface 实现了签名相同的方法，而且某个 interface 提供了默认实现，会产生接口冲突，需要在代码中明确指出调用的方法。

```java
class Student implements Person, Named {
    public String getName() { return Person.super.getName(); }
}
```

## interface 示例

### callback

Java 中的 callback 通常是传入一个对象，并且对象实现了指定的 interface，那么对方就能调用指定的 callback 函数了。

```java
class TinePrinter implements ActionListener {
    public void actionPerformed(ActionEvent event) {
        // ...
    }
}

ActionListener listener = new TimePrinter();
Timer t = new Timer(10000, listener);
```

### clone

`Object` 类中的 `clone()` 方法是 `protected` 的，因此不可以直接调用。如果要调用的话，需要自己实现 `Clonable` interface，同时重新定义 `clone()` 方法并设置为 `public`。

默认的 `clone()` 是一个浅拷贝，即 `clone()` 时对于成员不会递归地进行 `clone()`，只 `clone()` 一层。因此，如果成员是可变的，那么有必要自定义 `clone()` 方法（成员都是不可变的话，那显然就没必要了）。

```java
// 浅拷贝
class Employee implements Clonable {
    public Employee clone() throws CloneNotSupportedException {
        return (Employee) super.clone();
    }
}

// 深拷贝
class Employee implements Clonable {
    public Employee clone() throws CloneNotSupportedException {
        Employee cloned = (Employee) super.clone();

        // clone mutable fields
        cloned.hireDay = (Date) hireDay.clone();

        return cloned;
    }
}
```

如果 `clone()` 时某个对象不支持 `clone()`，那么就会抛出 `CloneNotSupportedException` 异常。

在继承关系中，`clone()` 可能会带来问题。如果父类实现了 `clone()`，那么就可以通过动态绑定进行子类的 `clone()`。如果子类没有定义 `clone()`，而且需要深拷贝或者存在不能拷贝的域，那么就会出错。

# Lambda Expr

## lambda expr 语法

匿名函数（参数类型可以由编译器推导）。

```java
(String first, String second) ->
{
    if (first.length() < second.length()) return -1;
    else if (first.length() > second.length()) return 1;
    else return 0;
}

// 推导参数类型

(first, second) ->
{
    if (first.length() < second.length()) return -1;
    else if (first.length() > second.length()) return 1;
    else return 0;
}

// 无参数 lambda 表达式

() -> { for (int i = 100; i >= 0; i-- ) System.out.println(i); }

// 单参数可推导类型 lambda 表达式

event -> System.out.println("The time is " + new Date());
```

lambda 表达式的类型可以让编译器进行推导。如果一个 lambda 表达式只在某些分支返回一个值，而在另外一些分支不返回值，那么是不合法的，如：`(int x) -> { if (x >= 0) return 1; }` 不合法。


## 函数式接口

只包含一个抽象方法的 interface 被称为函数式接口，可以用 lambda 表达式，即 lambda 表达式会被转换为接口。

Java 中没有函数类型，但是通过接口实现了 lambda 表达式。

### 常用函数式接口

| 函数式接口            | 参数   | 返回类型  | 抽象方法名 | 描述                         | 其他方法                         |
|-----------------------|--------|-----------|------------|------------------------------|----------------------------------|
| `Runnable`            | 无     | `void`    | `run`      | 作为无参数或返回值的动作运行 |                                  |
| `Supplier<T>`         | 无     | `T`       | `get`      | 提供一个 `T` 类型的值        |                                  |
| `Consumer<T>`         | `T`    | `void`    | `accept`   | 处理一个 `T` 类型的值        | `andThen`                        |
| `BiConsumer<T, U>`    | `T, U` | `void`    | `accept`   | 处理 `T` 和 `U` 类型的值     | `compose`，`andThen`，`identity` |
| `Function<T, R>`      | `T`    | `R`       | `apply`    | 有一个 `T` 类型参数的函数    | `andThen`                        |
| `BiFunction<T, U, R>` | `T, U` | `R`       | `apply`    | 有 `T` 和 `U` 类型参数的函数 | `compose`，`andThen`，`identity` |
| `UnaryOperator<T>`    | `T`    | `T`       | `apply`    | 类型 `T` 上的一元操作符      | `andThen`，`maxBy`，`minBy`      |
| `BinaryOperator<T>`   | `T, T` | `T`       | `apply`    | 类型 `T` 上的二元操作符      | `andThen`                        |
| `Predicate<T>`        | `T`    | `boolean` | `test`     | 布尔值函数                   | `and`，`or`，`negate`，`isEqual` |
| `BiPredicate<T, U>`   | `T, U` | `boolean` | `test`     | 有两个参数的布尔值函数       | `and`，`or`，`negate`            |

```java
public static void repeat(int n, Runnable action) {
    for (int i = 0; i < n; i++) action.run();
}

repeat(10, () -> System.out.println("Hello, World!"));
```

### 基本类型函数式接口

对于基本类型有特殊的接口，可以减少自动装箱，因此对于基本类型应该尽量使用这些接口。

| 函数式接口            | 参数   | 返回类型  | 抽象方法名     |
|-----------------------|--------|-----------|----------------|
| `BooleanSupplier`     | 无     | `boolean` | `getAsBoolean` |
| `PSupplier`           | 无     | `p`       | `getAsP`       |
| `PConsumer`           | `p`    | `void`    | `accept`       |
| `ObjPConsumer<T>`     | `T, p` | `void`    | `accept`       |
| `PFunction<T>`        | `p`    | `T`       | `apply`        |
| `PToQFunction`        | `p`    | `q`       | `applyAsQ`     |
| `ToPFunction<T>`      | `T`    | `p`       | `applyAsP`     |
| `ToPBiFunction<T, U>` | `T, U` | `p`       | `applyAsP`     |
| `PUnaryOperator`      | `p`    | `p`       | `applyAsP`     |
| `PBinaryOperator`     | `p, p` | `p`       | `applyAsP`     |
| `PPredicate`          | `p`    | `boolean` | `test`         |

`p, q` 为 `int, long, double`；`P, Q` 为 `Int, Long, Double`。

### 自定义函数式接口

自定义接口可以用 `@FunctionalInterface` 标记，保证 interface 满足函数式接口定义，并且在导出后 javadoc 会将其标记为函数式接口。

## 方法引用

### 普通方法引用

直接用方法名作为 lambda 表达式。

- `object::instanceMethod`：`System.out::println` 等价于 `x -> System.out.println(x)`，可以是 `this::instanceMethod` 或 `super::instanceMethod`
- `Class::static Method`：`Math::pow` 等价于 `(x, y) -> Math.pow(x, y)`
- `Class::instanceMethod`：第 1 个参数会成为方法的目标，即 `String::compareToIgnoreCase` 等价于 `(x, y) -> x.compareToIgnoreCase(y)`

如果由重栽方法，那么编译器会自行进行推断。

### 构造器引用

用 `new` 作为构造器的函数名，如 `Person::new` 等价于 `str -> Person(str)`。

```java
ArrayList<String> names = ...;
Stream<Person> stream = names.stream().map(Person::new);
List<Person> people = stream.collect(Collectors.toList());
```

## 变量作用域

- 自由变量：lambda 表达式可以捕获自由变量，但是要求捕获的变量值初始化后就不能改变，即隐式的 `final`
- 变量作用域：lambda 表达式中内部变量的作用域与外部相同，因此内部变量不能与外部同名

```java
Path first = Paths.get("/usr/bin");
Comparator<String> comp =
    (first, second) -> first.length() - second.length(); // first 与外部同名，错误
```

- `this`：lambda 表达式中使用 `this` 表示方法所在对象，而不是方法本身

```java
public class Application() {
    public void init() {
        ActionListener listener = event -> {
            System.out.println(this.toString()); // this 表示 Application 类
        }
    }
}
```

## Comparator

Comparator interface 包含很多 static 方法用于比较：
- `Comparator.comparing()` 将类型 `T` 映射到一个可以用于比较的类型，如 `Arrays.sort(people, Comparator.comparing(Person::getName));`
- `thenComparing()` 用于比较第二关键字，如 `Arrays.sort(people, Comparator.comparing(Person::getLastName).thenComparing(Person::getFirstName));`
- `comparing()` 和 `thenComparing()` 可以指定比较器：`Arrays.sort(people, Comparator.comparing(Person::getName, (s, t) -> Integer.compare(s.length(), t.length())));`
- 对于基本类型有特定的静态函数防止装箱：`Arrays.sort(people, Comparator.comparingInt(p -> p.getName().length()));`
- `naturalOrder()` 表示正向排序，`reverseOrder()` 等价于 `naturalOrder().reversed()` 表示逆向排序
- 如果比较内容可能为 `null`，可以用 `nullFirst(cmp)` 或 `nullLast(cmp)` 按照 `cmp` 排序并使 `null` 排在开头或末尾：`Arrays.sort(people, comparing(Person::getMiddleName, nulIsFirst(naturalOrder())));`

# 内部类

## 对象内部类

内部类只是定义在内部，不一定所有的外部类实例都有内部类成员。

```java
public class Outer {
    private int own = 1;
    public void outerMethod() {
        Inner inner = new Inner();
        inner.innerMethod();
    }

    private class Inner {
        public void innerMethod() {
            ++own; // 内部类可以引用外部类的变量
        }
    }
}
```

内部类可以访问外部类的成员。原理是内部类有一个外部类的隐式引用，可以通过它访问外部类成员。
并且由于内部类没有构造函数，所以编译器会生成一个构造函数，并传入 `this`。

```java
// 假设这个引用叫做 outer，实际上并不存在
public Inner(Outer o) {
    outer = o;
}

public void innerMethod() {
    ++outer.own;
}

// ...

Innter inner = new Outer(this);
```

只有内部类可以被声明为私有的，普通类要么是 `public`，要么是包内可见。

## 内部类的特殊语法规则

用 `OuterClassName.this` 表示外部类的引用。

```java
Outer.this.own++;
```

内部类对象的构造也可以用类似写法：`outerObject.new InnerClassName(args);`。在外部类的作用域外可以用 `OuterClassName.InnterClassName` 引用内部类。

```java
// 在外部类里面
this.new Inner();

// 在外部类外面
Outer outer = new Outer();
Outer.Inner inn = outer.new Inner();
```

内部类不能有 static 方法，防止语法太复杂。而且内部类的 static 成员必须是 final，因为严格看内部类是属于它的外部类的，不同外部类实例的内部类本质是不一样的，所以不应该共享数据，那样的话可变的 static 成员就没有意义了。

## 内部类的编译

内部类会被编译为 `Outer$Inner` 的形式，同时会在内部类中生成 `this$0` 来引用外部类对象（只有编译器能用）。同时，编译器允许内部类访问外部类的**私有域**。

同时编译器在外部类生成方法 `static int access$0(Outer)`。那么编译器会对内部类中使用外部成员的地方，使用这个函数。这个函数传入外部类引用，能返回对应的成员。（具体的更复杂）

```java
own++;
// 等价于
access$0(outer)++
```

## 局部内部类

内部类可以放在一个方法之中，称为局部类。局部类不需要访问控制符，因为它天然就被隐藏起来。

```java
public class Outer {
    private int own = 1;
    public void outerMethod() {
        private class Inner {
            public void innerMethod() {
                ++own; // 内部类可以引用外部类的变量
            }
        }
        Inner inner = new Inner();
        inner.innerMethod();
    }

}
```

局部类不仅能访问外部类，还能访问局部变量，前提是这些变量是 effectively final（虽然没用 `final` 修饰，但是不能改变的变量）的。

```java
public void outerMethod(int own) {
    private class Inner {
        public void innerMethod() {
            ++own;
        }
    }
    Inner inner = new Inner();
    // 假设 inner 在离开函数后仍然会用到，比如作为 callback
}

```

编译器会自动为这些变量创建拷贝，保证离开函数体后还能继续用。

```java
private class Inner {
    public void innerMethod()
    final int val$own; // 存储局部变量 own
    final Outer this$0;
}
```

## 匿名内部类

如果一个类只创建了一个对象，那么就不需要命名了。语法格式为

``` java
new SuperTypeName(args) { /* inner class */ }; // 不能忘记分号
```

其中，Super 可以是 interface，那么内部类要实现这个 interface。例如：

```java
ActionListener listener = new ActionListener() {
    public void actionPerformed(ActionEvent event) {
        // ...
    }
};
```

匿名类没有类名，所以也没有构造器。传递参数只传递给 SuperType 的构造器。

匿名类是在 lambda 表达式出现以前，用来替代 lambda 的一种手段。

### 匿名类的更多用法

除了替代 lambda 表达式，匿名类还有其他用法。

#### 双括号初始化

<!-- {% raw %} -->
```java
invite(new ArrayList<String> () {{ add ( "Harry "); add ("Tony"); }});
// 外面的 {} 表示一个匿名类
// 内部的 {} 表示一个对象构造块
```
<!-- {% endraw %} -->

#### `getClass()`

匿名类不能用 `getClass() != other.getClass()` 判断是不是一个类。

#### 获取静态方法名字

静态方法没有 `this`，所以在方法内部不能用 `getClass()`（本质上是 `this.getClass()`）获取名字。此时可以用内部类。

```java
new Object(){}.getClass().getEnclosingClass() // gets class of static method
```

这里首先通过 `getClass()` 得到匿名子类的匿名对象，然后通过 `getEnclosingClass()` 得到它的外部类，也就是静态方法所在的类。

## 静态内部类

如果只是想通过内部类来隐藏一个类，而不想使用外部类的引用，那么可以声明为静态内部类，取消产生的引用。

```java
public class Outer {
    private int own = 1;

    private static class Inner {
        public void innerMethod() { }
    }
}
```

此时访问 `Inner` 仍然需要通过 `Outer.Inner`，虽然不能访问外部类变量，但是也避免了 `Inner` 与外界名字冲突。
例如在某个类中返回了一个叫 `Pair` 的类，为了避免名字冲突，可以用 `Class.Pair` 来做到名字的隐藏。

静态内部类可以有静态域和静态方法，并且可以被外部类的静态方法使用。除此之外，静态内部类和内部类完全一样。

# 代理

## 代理的用处

代理可以实现在一个方法被调用前或被调用后执行一些用户指定的操作。例如调用后打印调用函数的信息，或者在调用前为被调用的函数过滤掉一些无效的调用。

个人理解，之所以叫做代理，是因为用户调用的是这个伪装函数，伪装函数干了一些自己的事情同时调用了真正的函数。

这里并不是说给函数加上全局的钩子！而是说给定一个类，以及要附加的操作（调用处理器），然后动态生成一个新的类，这个类就是原来的类的代理。然后必须要是这个动态生成的类的对象才能实现代理的效果。

代理类的用处主要是有时候想为某个类实现类似的效果，但是这样就要手写一个新的伴随类，而代理可以自动生成需要的代理类。

## 使用代理

使用代理分为三步。

首先要实现调用处理器（一个类）。这个类必须要实现 `InvocationHandler` 接口，在此接口中只有一个方法：

```java
Object invoke (Object proxy, Method method, Object[] args) // 代理对象，代理方法，代理方法参数
```

一个例子如下：

```java
class TraceHandler implements InvocationHandler {
    private Object target;

    public TraceHandler(Object t) {
        target = t;
    }

    public Object invoke(Object proxy, Method m, Object[] args) throws Throwable {
        // 调用前做一些事
        Object result = m.invoke(target, args);  // 调用真正的函数
        // 调用后做一些事
    }
}
```

然后使用 `Proxy.newProxyInstance()` 生成代理类（这个过程会反射），即利用代理在运行时创建一个实现了一组给定接口的新类。

```java
InvocationHandler handler = new TraceHandler (value);  // 创建调用处理器
Class[] interfaces = new Class[] { Comparable.class }; // 获取对象
Object proxy = Proxy.newProxyInstance(null, interfaces, handler); // 分别是类加载器，对象实现的方法，调用处理器
```

最后就可以使用 `proxy` 对象了，此时使用的 `proxy` 的类是动态生成的。只有通过 `proxy` 调用的函数才会被代理，并且函数必须要实现指定的 interfaces（例如上面的 `Comparable`，但是除此之外 `toString()` 等方法也会被默认代理）。

```java
proxy.equals(xxx); // 调用代理类
```

## 代理类的特性

代理类只有一个实例域，即调用处理器，如果要附加数据，那么必须添加在调用处理器中。

并且所有的代理类都默认覆盖了 `toString`/`equals`/`hashCode`，而其他方法没有。

对于特定的类加载器和相同的接口，只能实现一个代理类。这个类可以通过 `Proxy.getProxyClass(loader, interfaces)` 获取。同样，可以用 `Proxy.isProxyClass` 判断某个类是不是代理类。

代理类一定是 `public` 和 `final` 。如果代理类实现的所有接口都是 `public`，代理类就不属于某个特定的包；反之，所有非公有的接口都必须属于同一个包，而且，代理类也必须属于这个包。
