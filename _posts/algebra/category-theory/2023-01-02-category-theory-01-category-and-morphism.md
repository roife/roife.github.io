---
layout: "post"
title: "「范畴论」 01 范畴与态射"
subtitle: "Category and Morphism"
author: "roife"
date: 2023-01-02

tags: ["代数@数学", "数学@Tags", "范畴论@数学", "Haskell@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 范畴

一个范畴 $\mathcal{C}$ 由两个要素组成：
- 一组**对象**（object）：$A, B, C, \dots$，记作 $\operatorname{\mathrm{Ob}}(\mathcal{C})$
- 一组**态射**（morphism / arrow）
  + 该范畴上的所有态射组成的集合记作 $\operatorname{\mathrm{Arr}}(\mathcal{C})$
  + 对于 $A, B \in \operatorname{\mathrm{Ob}}(\mathcal{C})$，可以得到 $A \rightarrow B$ 的态射的集合 $\mathcal{C}(a, b)$（或记作 $\operatorname{\mathrm{Hom}}\_{\mathcal{C}}(A, B)$，称为 Hom 集）
  + 当 $a \ne a' \wedge b \ne b'$ 时，$\mathcal{C}(a, b) \cap \mathcal{C}(a', b') = \emptyset$

一个从 $a$ 到 $b$ 的态射可以记作 $f : a \rightarrow b$ 或 $a \overset{f}{\longrightarrow} b$。态射满足下面的性质：
- 对于每个 $a \in \operatorname{\mathrm{Ob}}(\mathcal{C})$，都存在**单位态射**（identity morphism） $\mathbf{1}_a \in \mathcal{C}(a, a)$
- 态射间存在**复合运算**（composition）：对于一对态射 $f : a \rightarrow b$ 与 $g : b \rightarrow c$，存在一个复合态射 $g \circ f : a \rightarrow c$，其中 $\circ$ 是态射复合的运算符。且复合运算 $\circ$ 满足结合律：设 $a \overset{f}{\longrightarrow} b,\ b \overset{g}{\longrightarrow} c,\ c \overset{h}{\longrightarrow} d$，有 $h \circ (g \circ f) = (h \circ g) \circ f$

这里的“对象”可以是任意的数学对象，例如值、类型、范畴等。“态射”是抽象的概念，不一定是映射，只要是满足上面定律的对象都可以成为态射。

## 范畴的例子

- 幺半群 $(m, 1, \otimes)$ 可以看作只有一个抽象对象的范畴：
  + $m$ 中的每个元素看作一个态射
  + 单位元 $\mathbf{1}$ 是 单位态射
  + 元素之间的乘积运算 $\otimes$ 对应态射的复合运算 $\circ$
- 偏序集合 $(s, \le)$ 满足自反性、反对称性、传递性可以看作一个范畴
  + 集合中的每个元素都是范畴中的一个对象
  + $\le$ 是态射，由自反性知存在单位态射，由传递性知态射可复合，且态射可结合
- Set 范畴
  + 对象是集合 $\mathtt{Set}\_A,\ \mathtt{Set}\_B,\ \cdots$
  + 态射是集合之间的映射 $\mathtt{Set}\_A \rightarrow \mathtt{Set}\_B$，显然映射可复合

## Haskell 中的范畴

Haskell 中能“近似”地定义范畴，一般讨论类型以及类型之间的映射：

```haskell
class Category cat where
  id  :: cat a a
  (.) :: cat b c -> cat a b -> a c
```

此处 `cat` 的 kind 为 `k -> k -> *`。`cat` 是一个范畴，对象是 `kind` 为 `k` 的类型（开启 `PolyKinds` 扩展），态射是 `cat a b`。

### Hask 范畴

由于 Haskell 中存在 `undefined`，所以 Haskell 中类型构成的的范畴并不是严格的 Set 范畴。

Haskell 中所有的**类型**以及**类型间的映射（函数）**构成了一个范畴。这个范畴称为 **Hask 范畴**：
- 对象为类型 `a :: *`
- 态射为 `(->) :: * -> * -> *`
- 态射复合 `(.)` 可结合
- 单位态射为 `id :: a -> a`

### 严格定义

Haskell 中类型间的映射都是 kind 为 `*` 的类型，函数也是 kind 为 `*` 的类型间的映射。因此在使用 `Category` 时，对象一般也是 kind 为 `*` 的类型。因此在标准库中将范畴直接定义为上面简化的 `Category` typeclass。

但是如果要严格定义 `Category`，那么应该在 typeclass 中声明一个类型家族来指定范畴上的对象类型。

```haskell
import Prelude hiding ((.), id)
import GHC.Types (Constraint)

class Category (cat :: k -> k -> *) where
  type Object cat (a :: k) :: Constraint
  id :: Object cat a => cat a a
  (.) :: (Object cat a, Object cat b, Object cat c) =>
         cat b c -> cat a b -> cat a c

instance Category (->) where
  type Object (->) (a :: *) = () -- () 当成 Constraint 表示没有 typeclass 限定
  id x = x
  (.) g f x = g (f x)
```

另外需要注意的一点是，上面在讨论的 kind 为 `*` 的类型中不包括 $\bot$，因为 $\bot$ 有任意的多态类型。所以下面在讨论 Haskell 和 Hask 范畴时不考虑 $\bot$、`undefined` 还有 `let x = x in x` 等。

## 反范畴（对偶范畴）

对于任意范畴 $\mathcal{C}$ , 其反范畴（Opposite Category） $\mathcal{C}^{\mathrm{op}}$ 定义如下：
- $\operatorname{\mathrm{Ob}}(\mathcal{C}^{\mathrm{op}}) = \operatorname{\mathrm{Ob}}(\mathcal{C})$
- 态射：$\forall a, b \in \operatorname{\mathrm{Ob}} (\mathcal{C}^{\mathrm{op}}), \mathcal{C}^{\mathrm{op}}(a, b) = \mathcal{C}(b, a)$
- 单位态射：$\mathcal{C}^{\mathrm{op}}$ 中的 单位态射与 $\mathcal{C}$ 相同
- 态射复合：$\forall f, g \in \operatorname{\mathrm{Arr}}(\mathcal{C}), g^{\mathrm{op}} \circ^{\mathrm{op}} f^{\mathrm{op}} = f \circ g$

反范畴可以理解为反转态射的箭头，其它都不变。因此反范畴的反范畴是自身，即 $(\mathcal{C}^{\mathrm{op}})^{\mathrm{op}} = \mathcal{C}$。

反范畴是原范畴的的对偶，例如原范畴的单一态射在反范畴中是完全态射，原范畴的初始对象在终极范畴中是终极对象。

```haskell
type Op a b = Op (getOp :: b -> a)
instance Category Op where
  id  = Op id
  Op f . Op g = Op (g .  f)
```

## 范畴的大小

范畴可以分成小范畴，大范畴和局部小范畴。这样的定义主要是为了避免罗素悖论。

如果范畴 $\mathcal{C}$ 的对象 $\operatorname{\mathrm{Ob}}(\mathcal{C})$ 和 $\operatorname{\mathrm{Arr}}(\mathcal{C})$ 都可以构成集合，那么称之为**小范畴**（small category）。反之，则称为**大范畴**（large category）。

例如集合范畴是一个大范畴（否则会构造出“集合的集合”）。

如果任意两个对象 $a, b \in \operatorname{\mathrm{Ob}}(\mathcal{C})$ 间的态射 $\mathcal{C}(a, b)$ 能构成集合，那称之为**局部小范畴**（locally small category）。局部小范畴的概念比小范畴更大一些。

一般来说小范畴比较少见，所以会讨论局部小范畴。

# 态射的性质

范畴论中推广了函数映射的一些性质，如单射、满射等。范畴论上的对象不再关系对象内部具体的内容，而只关心对象和态射，因此上面性质在范畴论上的推广用了另一套定义。对于范畴 $\mathcal{C}$ 上的态射 $f, g, h$，有以下定义:
- 完全态射（epimorphism）：若 $g \circ f = h \circ f \Rightarrow g = h$，则称 $f$ 为完全态射
  + 也称为右消除（right cancellation）或右可约
- 单一态射（monomorphism）：若 $f \circ g = f \circ h \Rightarrow g = h$,则 $f$ 是单一态射
  + 也称为左消除（left cancellation）或左可约
- 同构态射（isomorphism）：若对于 $f$，存在一个 $f^{-1}$ 满足 $f \circ f^{-1} = \operatorname{\mathrm{id}}$ 且 $f^{-1} \circ f = \operatorname{\mathrm{id}}$,则称 $f$ 是同构态射

单一态射是单射的推广，完全态射是满射的推广，同态态射是双射的推广。但是和函数映射仍然有区别。例如单射 + 满射 = 双射；而单一态射 + 完全态射 = 双态射（bimorphism），不一定是同构态射。

# 初始对象和终极对象

一些范畴内有两种特殊的对象：
- 对于范畴 $\mathcal{C}$，如果对于所有对象 $A \in \operatorname{\mathrm{Ob}}(\mathcal{C})$ 都有**唯一态射** $\mathbf{0} \rightarrow A$，则 $\mathbf{0}$ 称为**初始对象**（initial object）
- 对于范畴 $\mathcal{C}$，如果对于所有对象 $A \in \operatorname{\mathrm{Ob}}(\mathcal{C})$ 都有**唯一态射** $A \rightarrow \mathbf{1}$，则 $\mathbf{1}$ 称为**终极对象**（terminal object）

范畴中的初始对象与终极对象**唯一同构（unique up to isomorphism）**：
- 如果存在另一个初始对象 $\mathbf{0'}$，那么 $\mathbf{0} \simeq \mathbf{0'}$
- 如果存在另一个终极对象 $\mathbf{1'}$，那么 $\mathbf{1} \simeq \mathbf{1'}$

Hask 范畴内的初始对象与终极对象分别为 `Void` 与 `Unit`（这里不考虑 `undefined`，否则 Haskell 就无法给出范畴的初始对象和终极对象了）：

```haskell
data Void
data Unit = Unit

absurd :: Void -> a
absurd = absurd

unit :: a -> Unit
unit _ = Unit
```

`()` 和 `Unit` 同构，其它空对象也和 `Void` 同构：

```haskell
data V
data U = U

vphi :: V -> Void
vphi = vphi

vpsy :: Void -> V
vpsy = absurd

uphi :: U -> Unit
uphi U = Unit

upsy :: Unit -> U
upsy Unit = U
```
