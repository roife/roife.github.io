---
layout: "post"
title: "「PKU - Software Analysis」 01 Introduction"
subtitle: "停机问题，Rice's Theorem 与 Must/May Analysis"
author: "roife"
date: 2021-10-07

tags: ["程序分析@Tags", "北大软件分析@课程相关", "课程相关@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 哥德尔不完备定理

> 包含自然数和基本算术运算（如四则运算）的一致系统一定不完备

- 完备性：所有真命题都可以被证明
- 一致性：公理系统不可能推出矛盾，即一个命题要么是真，要么是假，不会两者都是

现今主流编程语言的语法和语义都能表达自然数系统，所以他们的表达式可能存在无法证明的情况

# 可判定问题

> 是一个「判定问题」，该问题存在一个算法，使得对于该问题的每一个实例都能给出是/否的答案。
>
> - 停机问题是不可判定问题
> - 确定程序有无内存泄露是不可判定问题

## 停机问题

> 判断一个程序在给定输入上是否会终止。

### 证明

- 设存在停机问题判断算法：`bool Halt(Program p)`
- 给定程序
  ```c
  void Evil() {
      if (!Halt(Evil)) return;
      else while(1); // diverge
  }
  ```
- 调用 `Halt(Evil)` 产生矛盾：
  + 如果 `Halt(Evil) = true`，则 `!Halt(Evil) = true`，`Halt(Evil) = false`，矛盾
  + 如果 `Halt(Evil) = false`，则 `!Halt(Evil) =false`，`Halt(Evil) = true`，矛盾

## 是否存在确保无内存泄露的算法？

- 设存在内存泄漏问题判断算法：`bool LeakFree(Program p)`
- 给定程序
  ```c
  void Evil() {
      int a = malloc();
      if (LeakFree(Evil)) return; // leak
      else free(a);
  }
  ```
- 同理，会产生矛盾

# Rice's Theorem

> 把**任意程序**看成一个从输入到输出上的函数（输入输出对的集合），该函数描述了程序的行为。关于该函数/集合的任何非平凡属性（非永真或永假的属性），都不存在可以检查该属性的通用算法。

判断是否能使用 rice's theorem：*看能不能直接通过输入输出定义这种属性*

> 如下程序分析问题是否可判定？
>
> - 确定程序使用的变量是否多于 50 个（可以，不能用 rice's theorem）
> - 给定程序，判断是否存在输入使得该程序抛出异常（不行，可能无法停机，$\exists i, f(i) = \operatorname{\mathtt{EXCEPT}}$）
> - 给定程序和输入，判断程序是否会抛出异常（等价于上题）
> - 给定无循环和函数调用的程序和特定输入，判断程序是否会抛出异常（可以，但是不能用 rice's theorem，因为不是对所有程序）

**不符合 Rice's Theorem 不代表可判定。**

## 证明：转换为停机问题

- 给定函数上的非平凡性质 $P$
- 假设 $\emptyset$（对任何输入都不输出的程序，相当于会死循环的程序）不满足 $P$
  - 因为 $P$ 非平凡，所以一定存在程序使得 $P$ 满足，记为 `ok_prog`
  - 假设检测该性质 $P$ 的算法为 `P_holds`
  - 那么下面这个程序可以检测 $q$ 是否停机，与停机问题矛盾
    ```c
    Bool halt(Program q) {
        void evil(Input n) {
            Output v = ok_prog(n);
            q();
            return v;
        }

        return P_holds(evil);
    }
    ```
    + 如果 $q$ 停机，那么就会返回 $v = \operatorname{\mathtt{ok\\_prog}}(n)$ 使得 `P_holds` 成立，返回真
    + 如果 $q$ 不停机，那么就不会有返回（返回 $\emptyset$），`P_holds` 不成立，返回假
- 如果 $\emptyset$ 满足 $P$，定义一个 `not_ok_prog`

# 一个特殊的停机检测算法

- 当前系统的状态为内存和寄存器中所有 Bit 的值。给定任意状态，系统的下一状态是确定的
- 令系统的所有可能的状态为节点，状态 A 可达状态 B 就添加一条 A 到 B 的边，那么形成一个有向图
- 给定起始状态，遍历执行路径，同时记录所有访问过的状态
- 如果有达到一个之前访问过的状态，则有环。如果达到终态，则无环
- 因为状态数量有穷，所以该算法一定终止

假设下面的程序：

```c
void Evil() {
    if (!Halt(Evil)) return;
    else while(1);
}
```

`Halt` 要调用 `Evil`，`Evil` 又要调用 `Halt`，此时需要无穷多个状态。

但是对于不会调用 `Halt` 的程序可以工作（Model Checking，常用于硬件）。

# Must/May analysis

允许对于部分问题输出“不知道”。

- **must analysis**：只输出“是”或者“不知道”（lower/under approximation）
- **may analysis**：只输出“否”或者“不知道”（upper/over approximation）

设肯定答案集合为 $S$，否定答案集合为 $\operatorname{\mathtt{NEVER}}$，则：

$$
\begin{aligned}
& \operatorname{\mathtt{MUST}} \subseteq S \\
& \operatorname{\mathtt{NEVER}} \cap S = \emptyset \\
& S \supseteq \operatorname{\mathtt{MUST}} \cup \operatorname{\mathtt{MAY}}
\end{aligned}
$$

- 测试是 MUST 分析（测试通过不一定没问题，不通过一定有问题）
- 类型检查是 MAY 分析（类型检查通过一定没问题，不通过不一定有问题）
  + 有可能类型检查不通过的部分不可达（例如在某个永假的 `if` 里面）
  + Java 要求 caller 必须处理 callee 声明的所有异常，但是有可能 callee 运行时不会抛出异常，此时虽然程序没问题但是无法通过类型检查

## Soundness 和 Completeness

Soundness 可以理解成 Safety 或者 correctness，其反面就是 Completeness。

# 求近似解基本方法

## 抽象

例如判定 `a + b * c` 当输入都是正数，判断输出是否为正数。

定义**抽象域**：
- `正 = {所有的正数}`
- `零 = {0}`
- `负 = {所有的负数}`
- `不知道 = {所有的整数和 NaN}`

对于任意两个输入及一个运算符，都可以确定一个属于上面几种情况的输出。

## 搜索

遍历所有输入，判断性质是否成立。如果搜索超时则为“不知道”。

需要用启发式的方法并合理剪枝。
