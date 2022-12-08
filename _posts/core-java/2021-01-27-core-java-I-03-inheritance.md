---
layout: "post"
title: "「Core Java」 03 Inheritance"
subtitle: "继承"
author: "roife"
date: 2021-01-27

tags: ["Java@编程语言", "Core Java@读书笔记", "读书笔记@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 继承

Java 中所有继承都是 `public` 的，继承用 `extend` 表示。

```java
public class Manager extends Employee {
    // ...
}
```

已经存在的类被称为 superclass/base class/parent class，新的类被称为 subclass/derived class/child class。

## 覆盖方法

子类不能直接访问父类的私有成员，只能通过对应的方法访问。如果子类和父类重名，可以用 `super` 访问。

覆盖方法不需要声明为虚方法，即默认会发生动态绑定。

```java
public double getSalary() {
    double baseSalary = super.getSalary(); // C++ 中是 Employee::getSalary
    return baseSalary + bonus;
}
```

## 子类构造器

子类必须用父类的构造器（`super`）对父类成员进行初始化。（C++ 中在初始化列表调用类名）

```java
public Manager(String name, double salary, int year, int month, int day) {
    super(name, salary, year, month, day);
    bonus = 0;
}
```

## 多态

父类变量可以引用子类对象，但是不能反过来。（类似于 C++ 的一套绑定机制）

```java
Employee e;
boss = new Manager(. . .);

Employee[] staff = new Employee[3];
staff[0] = boss;

boss.setBonus(5000);      // OK
staff[0].setBonus(5000);  // Error
```

## 方法调用

1. 编译器找到与签名匹配的方法
2. 如果是 `private`/`static`/`final` 方法则发生静态绑定
3. 否则根据调用者的类型发生动态绑定

类似于 C++，Java 会在一个方法表中查询对应的方法。

## `final`

`final` 可以用来阻止某个类被拓展，或者阻止某个方法被覆盖。（意思就是已经是最终版本了）

```java
public final class Executive extends Manager {
    // ...
}

public class Employee {
    public final String getName() {
        // ...
    }
}
```

## 强制类型转换

类似于 C++ 的 `dynamic_cast`，要把父类引用的对象还原成子类。为了防止发生错误，在转换之前先进行检验。

一般多态能够使用所有发生动态绑定的方法，进行类型转换是为了使用子类特有的方法。

```java
if (staff instanceof Manager) {
    boss = (Manager) staff;
    // ...
}
```

## 抽象类

抽象方法类似于 C++ 的纯虚函数，其类不能实例化，用 `abstract` 修饰。
含有抽象方法的类也要用 `abstract` 修饰。

```java
public abstract class Person {
    public abstract String getDescription() {
        // ...
    }
}
```

如果子类不实现抽象类的所有抽象方法，则子类也是一个抽象类。

## `protected`

类似 C++，对本包和所有子类可见。

# `Object` 类

`Object` 类是 Java 中所有类的始祖，所以使用 `Object` 类型的变量可以引用任何类型的对象。

## `equals`

函数签名应当是 `equals(Object)`。

重载 `equals` 时要考虑到自己的成员为 `null` 的情况，所以应该调用 `Objects.equals()`。

```java
public class Employee {
    public boolean equals(Object otherObject) {
        // a quick test to see if the objects are identical
        if (this == otherObject) return true;

        // must return false if the explicit parameter is null
        if (otherObject == null) return false;

        // if the classes don't match, they can't be equal
        if (getClass() != otherObject.getClass()) return false;

        // now we know otherObject is a non-null Employee
        Employee other = (Employee) otherObject;

        // test whether the fields have identical values
        return Object.equals(name, other.name)
                    && salary == other.salary
                    && Object.equals(hireDay, other.hireDay);
    }
}
```

对于子类，则需要先比较父类。

```java
if (!super.equals(otherObject)) return false;
// super.equals checked that this and otherObject belong to the same class
Manager other = (Manager) otherObject;
return bonus == other.bonus;
```

### 相等与继承

写 `equals` 比较是否来自同一个相等的类时，会遇到两种情况：
- 如果子类能够拥有自己的相等概念，则应该使用 `getClass()` 来比较来保证对称性
- 如果由超类决定相等的概念，那么就可以使用 `instanceof` 进行检测，这样可以在不同子类的对象之间进行相等的比较

前者比如 `Manager` 继承自 `Employee`。比较二者只需要比较姓名和编号。如果 `e.equals(m)` 返回真，那么根据对称性反过来也成立。但是用 `m instanceof Employee` 是真，`e instanceof Manager` 是假，不符合对称性规则。所以要用 `getClass()`。

后者的情况如 `TreeSet` 和 `HashSet` 都是集合，继承自 `AbstractSet`，比较二者应该比较是否都是相同的元素（即从集合的概念上比较），而不需要比较树和哈希这两个实现方法，所以应该用 `instanceof AbstractSet`。

## `hashCode()`

计算对象的散列值。如果重新定义了 `equals`，那么也要重新定义 `hashCode` 保证相等的对象散列相同。

```java
public int hashCode() {
    // 用 Object.hash 或者 xxx.hashCode 可以避免 null 的情况
    // 对于基本类型可以用 Double.hashCode / etc
    return Object.hash(name, salary, hireDay);
}
```

对于数组，可以用 `Array.hashCode()`。

## `toString()`

大多数 `toString()` 遵循 `ClassName[a=1, b=2]` 这样的形式。类名可以用 `getClass()` 得到。

```java
public String toString() {
  return getClass().getName()
    + "[name=" + name
    + ",salary: " + salary
    + ",hireDay=" + hireDay + T;
}
```

对于子类也要自定义。如果父类方法使用了 `getClass().getName()`，此时得到的就是子类的类型，不用再变了，直接用 `super.toString()`。

```java
public class Manager extends Employee {
    public String toString() {
        return super.toString()
        + "[bonus=" + bonus + "]";
    }
}
```

如果字符串和一个对象用 `+` 相连，则 Java 会自动调用 `toString()` 方法。同理，调用 `print()` 时也会自动调用 `toString()`。但是对于数组不能这么做，要用 `Array.toString()`。

```java
Point p = new Point(10, 20);
String message = "The current position is " + p;
```

# `ArrayList`

类似于 C++ 的 `vector`。

```java
ArrayList<Employee> staff = new ArrayList<>(); // 右边可以省略类型名
staff.add(new Employee());
```

# 对象包装器与自动装箱

基本类型也有对应的类，即 `Integer`、`Long`、`Float`、`Double`、`Short`、`Byte`、`Character`、`Void` 和 `Boolean`。前六个又属于 `Number` 类。

由于 `ArrayList` 只能装对象，此时需要把基本类型转为对象。

```java
ArrayList<Integer> list = new ArrayList<>();
```

但是在使用时不需要进行类型转换，可以**自动装箱**。

```java
list.add(3); // 即 list.add(Integer.valueOf(3));
int n = list.get(i); // 即 int n = list.get(i).intValue();
```

但是不可以把这些对象看作基本类型。

```java
Integer a = 1000;
Integer b = 1000;
if (a == b) // 不一定成立，应该用 equals
```

注意，包装器是不可变的。如果需要可变的对象包装类型需要用 `IntHolder` 等。

```java
public static void triple(Integer x) { // won't work
    x = x * 3; // 无效
}
```

# 可变参数方法

变参部分看作一个数组。

```java
public PrintStream printf(String fmt, Object... args) { return format(fmt, args); }

// 编译器自动转换
// System.out.printf("M Xs", new Object[] { new Integer(n), "widgets" } );
```

# 枚举类

```java
public enum Size {
    SMALL("S") , MEDIUM("M") , LARGE("L") , EXTRA_LARGE("XL") ;
    private String abbreviation;
    private Size(String abbreviation) { this, abbreviation = abbreviation; }
    public String getAbbreviation() { return abbreviation; }
}
```

# 反射

## `Class` 类

`Class` 类保存了对象的类型信息。
- `Class`
  + `static Class forName(String className)`：返回描述类名为 className 的 Class 对象。
  + `Object newInstance()`：返回这个类的一个新实例
  + `String getName()`：获取类名，包括包名


- `Class getClass()`：获取 `Class` 类
- `obj.class`：获取 `Class` 类（可以对基本类型使用）

```java
Class cl = e.getClass();
String name = cl.getName();
Class cl2 = Class.forName(name);
```

对数组获取类名时，会用特殊的显示方式：`Double[].class.getName()` 返回 `[Ljava.lang.Double;`

## 用反射分析类

`java.lang.reflect` 包中有三个类 `Field`、`Method`、`Constructor`。
- 每个类都有一个 `getName()` 方法
- 每个类都有一个 `getModifiers` 方法返回一个整数，报告访问控制符
- `Field` 有一个 `getType()` 方法返回对应的 `Class` 对象
- `Method` 和 `Constructor` 可以报告参数
- `Method` 可以报告返回类型

`java.lang.reflect` 中还有一个 `Modifier` 类的静态方法可以分析控制符。

`Class` 类的 `getFields`、`getMethods` 和 `getConstructors` 方法可以返回数组，内含 `public` 成员（包括父类的 `public` 成员）。`getDeclareFields`、`getDeclareMethods` 和 `getDeclaredConstructors` 方法可以获得类的全部成员，但是不包括父类的成员。

- `java.lang.Class`
  + `Field[] getFields()`：返回一个包含 `Field` 对象的数组，这些对象记录了这个类或其超类的公有域。
  + `Field[] getDeclaredFie1ds()`：返回包含 `Field` 对象的数组，这些对象记录了这个类的全部域。
  + `Method[] getMethods()`：返回所有的公有方法，包括从超类继承来的公有方法
  + ……
- `java.lang.reflect.Field`
- `java.lang.reflect.Method`
- `java.lang.reflect.Constructor`
  + `Class getDeclaringClass()`：返冋一个用于描述类中定义的构造器、方法或域的 `Class` 对象
  + ……
- `java.lang.reflect.Modifier`
  + `static String toString(int modifiers)`：返回对应 `modifiers` 中位设置的修饰符的字符串表。
  + `static boolean isAbstract(int modifiers) `
  + ……

## 分析类

输入类名，输出类的结构：

```java
package reflection;

import java.util.*;
import java.lang.reflect.*;

/**
 * This program uses reflection to print all features of a class.
 * @version 1.1 2004-02-21
 * @author Cay Horstmann
 */
public class ReflectionTest
{
   public static void main(String[] args)
   {
      // read class name from command line args or user input
      String name;
      if (args.length > 0) name = args[0];
      else
      {
         Scanner in = new Scanner(System.in);
         System.out.println("Enter class name (e.g. java.util.Date): ");
         name = in.next();
      }

      try
      {
         // print class name and superclass name (if != Object)
         Class cl = Class.forName(name);
         Class supercl = cl.getSuperclass();
         String modifiers = Modifier.toString(cl.getModifiers());
         if (modifiers.length() > 0) System.out.print(modifiers + " ");
         System.out.print("class " + name);
         if (supercl != null && supercl != Object.class) System.out.print(" extends "
               + supercl.getName());

         System.out.print("\n{\n");
         printConstructors(cl);
         System.out.println();
         printMethods(cl);
         System.out.println();
         printFields(cl);
         System.out.println("}");
      }
      catch (ClassNotFoundException e)
      {
         e.printStackTrace();
      }
      System.exit(0);
   }

   /**
    * Prints all constructors of a class
    * @param cl a class
    */
   public static void printConstructors(Class cl)
   {
      Constructor[] constructors = cl.getDeclaredConstructors();

      for (Constructor c : constructors)
      {
         String name = c.getName();
         System.out.print("   ");
         String modifiers = Modifier.toString(c.getModifiers());
         if (modifiers.length() > 0) System.out.print(modifiers + " ");
         System.out.print(name + "(");

         // print parameter types
         Class[] paramTypes = c.getParameterTypes();
         for (int j = 0; j < paramTypes.length; j++)
         {
            if (j > 0) System.out.print(", ");
            System.out.print(paramTypes[j].getName());
         }
         System.out.println(");");
      }
   }

   /**
    * Prints all methods of a class
    * @param cl a class
    */
   public static void printMethods(Class cl)
   {
      Method[] methods = cl.getDeclaredMethods();

      for (Method m : methods)
      {
         Class retType = m.getReturnType();
         String name = m.getName();

         System.out.print("   ");
         // print modifiers, return type and method name
         String modifiers = Modifier.toString(m.getModifiers());
         if (modifiers.length() > 0) System.out.print(modifiers + " ");
         System.out.print(retType.getName() + " " + name + "(");

         // print parameter types
         Class[] paramTypes = m.getParameterTypes();
         for (int j = 0; j < paramTypes.length; j++)
         {
            if (j > 0) System.out.print(", ");
            System.out.print(paramTypes[j].getName());
         }
         System.out.println(");");
      }
   }

   /**
    * Prints all fields of a class
    * @param cl a class
    */
   public static void printFields(Class cl)
   {
      Field[] fields = cl.getDeclaredFields();

      for (Field f : fields)
      {
         Class type = f.getType();
         String name = f.getName();
         System.out.print("   ");
         String modifiers = Modifier.toString(f.getModifiers());
         if (modifiers.length() > 0) System.out.print(modifiers + " ");
         System.out.println(type.getName() + " " + name + ";");
      }
   }
}
```

```java
package objectAnalyzer;

import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;

public class ObjectAnalyzer
{
   private ArrayList<Object> visited = new ArrayList<>();

   /**
    * Converts an object to a string representation that lists all fields.
    * @param obj an object
    * @return a string with the object's class name and all field names and
    * values
    */
   public String toString(Object obj)
   {
      if (obj == null) return "null";
      if (visited.contains(obj)) return "...";
      visited.add(obj);
      Class cl = obj.getClass();
      if (cl == String.class) return (String) obj;
      if (cl.isArray())
      {
         String r = cl.getComponentType() + "[]{";
         for (int i = 0; i < Array.getLength(obj); i++)
         {
            if (i > 0) r += ",";
            Object val = Array.get(obj, i);
            if (cl.getComponentType().isPrimitive()) r += val;
            else r += toString(val);
         }
         return r + "}";
      }

      String r = cl.getName();
      // inspect the fields of this class and all superclasses
      do
      {
         r += "[";
         Field[] fields = cl.getDeclaredFields();
         AccessibleObject.setAccessible(fields, true);
         // get the names and values of all fields
         for (Field f : fields)
         {
            if (!Modifier.isStatic(f.getModifiers()))
            {
               if (!r.endsWith("[")) r += ",";
               r += f.getName() + "=";
               try
               {
                  Class t = f.getType();
                  Object val = f.get(obj);
                  if (t.isPrimitive()) r += val;
                  else r += toString(val);
               }
               catch (Exception e)
               {
                  e.printStackTrace();
               }
            }
         }
         r += "]";
         cl = cl.getSuperclass();
      }
      while (cl != null);

      return r;
   }
}
```

## 在运行时使用反射分析对象

- `java.lang.reflect.AccessibleObject`
  + `void setAccessible(boolean flag)`：为反射对象设置可访问标志。`flag` 为 `true` 表明屏蔽 Java 语言的访问检查，使得对象的私有属性也可以被査询和设置。
  + ……
- `java.lang.Class`
  + `Field getField(String name)`
  + ……
- `java.Iang.reflect.Field`
  + `Object get(Object obj)`
  + ……

## 反射泛型数组

- `java.lang.reflect.Array`
  + `static Object get(Object array, int index)`
  + `static xxx getXxx(Object array, int index)`（xxx 是基本类型）
  + ……

在数组上应用反射需要三步：
- 获取数组的类对象，并且确认这是一个数组
- 使用 `Class` 类的 `getComponentType()` 方法获取数组成员的类型

```java
public static Object goodCopyOf(Object a, int newLength) { // 注意返回类型
  Class cl = a.getClass();
  if (!cl.isArrayO) return null;
  Class componentType = cl.getComponentType();
  int length = Array.getLength(a);
  Object newArray = Array.newlnstance(componentType, newLength);
  System.arraycopy(a, 0, newArray, 0, Math.min(length, newLength));
  return newArray;
}
```

## 调用任意方法

- `java.lang.reflect.Method`
  + `public Object invoke(Object implicitParameter, Object... explicitParameters)`：调用这个对象所描述的方法，传递给定参数，并返回方法的返回值。
    对于静态方法，把 `null` 作为隐式参数传递。在使用包装器传递基本类型的值时，基本类型的返回值必须是未包装的。
