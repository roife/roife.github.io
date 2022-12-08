---
layout: "post"
title: "「System Verilog」 07 面向对象"
subtitle: "OOP in SV"
author: "roife"
date: 2022-10-23

tags: ["System Verilog@编程语言", "集成电路@Tags", "SV for Verification@读书笔记"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 类

SV 中可以在 `program`/`module`/`package` 中定义类。

```verilog
class ClassName;
    // ...
endclass : ClassName
```

SV 中的 OOP 有几个新的概念：
- 句柄（handle）：指向对象的**引用**
- 原型（prototype）：类似于函数签名，包括程序名、返回类型和参数列表

相比起 C++，SV 的 OOP 更加贴近于 Java（有垃圾回收、句柄只支持对象的引用等）。

# 对象创建/销毁/访问

调用 `new()` 函数时取决于赋值操作符**左侧句柄的类型**。

```verilog
Transaction tr;    // 创建一个对象的句柄，初始值为 null
tr = new();        // 分配空间
```

这里同样需要注意的是，如果程序没有用 `automatic` 指定栈式空间分配，那么也不应该在声明时直接调用构造函数（即不应该直接用 `A a = new()`，这样是静态分配）。

## 定义构造函数

构造函数会分配内存，并初始化变量（二值类型初始化为 `0`，四值类型初始化为 `X`）。

```verilog
function new(args);
    // ...
endfunction
```

## 内存释放

想要释放内存则直接将句柄赋值为 `null` 即可，因为 SV 支持垃圾回收。

## 对象访问

一般来说 OOP 最好用 getter/setter 来操作对象，但是在 SV 中为了方便利用随机化来建立测试平台，一般会将变量设置为公有。

## `this` 指针

类似于 C++ 的 `this`。

# 方法定义

## 类内定义方法

SV 的方法就是类内定义的 `task` 和 `function`，调用方法类似其他语言，通过句柄实现。

## 类外定义方法

类外定义方法的语法类似于 C++，但是需要在类内通过 `extern` 进行声明：

```verilog
class Transaction;
    extern function void f();   // 声明方法
endclass

function void Transaction::f(); // 定义方法
endfunction
```

不同的是 SV 要求类内声明和类外定义的签名一致。

# 静态变量与静态方法

## 静态变量

SV 中可以通过句柄或者类名访问静态变量。由于静态变量类似于全局变量，因此一般在**声明时**初始化。

```verilog
class Transaction;
    static int count = 0;    // 静态变量定义
endclass

Transaction t1;
t1 = new();

t1.count                     // 访问静态变量
Transaction::count           // 通过类名访问
```

## 静态方法

静态方法的定义和调用类似于静态变量。

```verilog
class Transaction;
    static function void f();
    endfunction
endclass
```

# 用 `typedef` 声明未定义的类

如果定义的类里面用到了一个未定义的类，则需要用 `typedef` 进行声明：

```verilog
typedef class B;

class A;
    // ...
endclass

class B;
    // ...
endclass
```

# 对象复制

## `new`

可以用 `new` 进行对象拷贝：

```verilog
dst = new src;
```

但是这里同样存在深浅拷贝的问题：这种普通的复制只会单纯复制所有的变量，如果其中有句柄引用了其他对象，那么需要手动编写拷贝函数。

## 拷贝函数

```verilog
class Transaction;
    Statistics stats;    // 需要深拷贝的对象
    int id;              // 其他字段

    // ...

    function Transaction copy;
        copy = new();
        copy.id = id;
        copy.stat = stat.copy();
    endfunction
endclass
```

## 打包成员（序列化）

```verilog
class Transaction;
    bit [31:0] addr, crc, data[8];

    function void pack(ref byte bytes[40]);
        bytes = {>>{addr, crc, data}};
    endfunction

    function void unpack(ref byte bytes[40]);
        {>>{addr, crc, data}} = bytes;
    endfunction
endclass
```

# 可见性

在 SV 中，默认所有成员都是**公有**的，除非被标记为  `local` 或 `protected`。

## `local`

`local` 类似于 `private`，只能被相同的类访问到，并且不能被子类访问：

```verilog
class ABC;
  local byte local_var;

  local function void f();
    // ...
  endfunction
endclass
```

## `protected`

类似于其他语言。

# 继承

## `extend` 与 `super`

SV 中的继承通过 `extends` 关键字实现，并且可以用 `super` 来访问父类的成员和方法。

子类的构造函数必须在第一行调用 `super.new()`（即父类的构造函数）。

```verilog
class networkPkt extends myPacket;
	bit        parity;

	function new ();
		super.new ();
		this.parity = 1;
	endfunction
endclass
```

## 虚方法

SV 的多态规则类似于 Java，如果方法不是虚方法，或者没有被重写，那么调用的是父类的方法。虚方法的定义如下：

```verilog
class Transaction;
    virtual function void doTransaction ();
        // ...
    endfunction
endclass

class SubTransaction extends Transaction;
    virtual function void doTransaction ();
        // ...
    endfunction
endclass
```

子类的虚方法和父类的虚方法具有相同的方法签名。

## 类型转换

可以将子类的对象赋值给父类句柄，此时只能访问父类成员。如果需要将父类对象转换为子类对象，则需要用 `$cast`。

```verilog
subclass = new();

baseclass = subclass;

$cast(subclass, baseclass);     // 向下转型，subclass = baseclass
```

# 抽象类与纯虚方法

只能在抽象类内才可以定义纯虚方法，并且只有所有纯虚方法都被实现了，类才可以被实例化。

```verilog
virtual class Base;         // 定义抽象类
    pure virtual function void f ();    // 定义纯虚方法
endclass
```

# 参数化类

SV 中参数化类的语法为：

```verilog
class <ClassName> #(<param_type> <param_name> = <default_value>);
    // ...
endclass

<name_of_class> #(<parameters>) objs;
```

## 泛型

SV 支持将类型作为类的参数传入，以实现泛型，其参数类型为 `type`。例如下面定义了一个栈：

```verilog
class stack #(type T = int);
  T item;

  function T add_a (T a);
    return item + a;
  endfunction
endclass

stack #(bit[3:0]) 	bs;
```

## 其他类型

SV 中的参数化类还支持其他类型的参数，例如 `int`、`real`、`string` 等。

```verilog
class Queue #(int size = 8);
	bit [size-1:0] out;
endclass

Queue #(16) q;
```

# 虚接口

在验证中可能需要对相同类型的接口进行同样的测试，此时就需要在验证时复用测试代码。通常接口和 DUT 一样，属于硬件范畴，因此需要在仿真开始时就实现；而基于 OOP 的仿真测试平台属于软件的范畴，会在运行过程中动态实例化。

因此在使用 OOP 的实验环境中，不能直接在类中创建接口，而是需要在类中创建虚接口（`virtual interface`），然后在实例化类时，将接口传入。

虚接口可以看成物理接口的句柄。

```verilog
class myClass;
    virtual Rx_if.port Rx0;
    // ...
endclass
```
