+++
title = "LLVM 如何构造 SSA：Mem2Reg Pass"
author = ["roife"]
date = 2022-02-07
tags = ["编译器", "LLVM", "SSA构建"]
draft = false
+++

## 介绍 {#介绍}

Mem2Reg 是 LLVM 采用的 SSA 转换算法。如果使用 LLVM 作为后端，编译器前端在生成 LLVM IR 时可以先生成 `alloca` / `load` / `store` 这样借助内存存储局部变量值的 SSA 形式（即可以先不生成 \\(\varphi\\) 函数）。在 LLVM 拿到前端生成的代码后，Mem2Reg 会将这些指令删除，并插入合适的 \\(\varphi\\) 函数。

例如下面这段代码：

```C
int main() {
    int x, cond = 1;
    if (cond > 0)
        x = 1;
    else
        x = -1;
    return x;
}
```

前端生成的代码：

```llvm
define dso_local i32 @main() {
    %1 = alloca i32
    %2 = alloca i32
    store i32 1, i32* %1
    %3 = load i32, i32* %1
    %4 = icmp sgt i32 %3, 0
    br i1 %4, label %5, label %8

5:
    store i32 1, i32* %2
    br label %6

6:
    %7 = load i32, i32* %2
    ret i32 %7

8:
    %9 = sub i32 0, 1
    store i32 %9, i32* %2
    br label %6
}
```

Mem2Reg 转换后的代码：

```llvm
define dso_local i32 @main() {
    %1 = icmp sgt i32 1, 0
    br i1 %1, label %2, label %5

2:
    br label %3

3:
    %4 = phi i32 [ 1, %2 ], [ %6, %5 ]
    ret i32 %4

5:
    %6 = sub i32 0, 1
    br label %3
}
```


## 算法原理 {#算法原理}

Mem2Reg 的算法过程和构建 SSA 的过程非常像，分为两个阶段：

1.  在支配边界**插入 \\(\varphi\\) 指令**（支配边界可以理解为“恰好支配不到的基本块”）
    -   假设在 `B` 处 `store`，那么在 `DF(B)` 中的基本块被支配，可能有其它分支的值流向它，需要插入 \\(\varphi\\)
    -   插入 \\(\varphi\\) 后，流向支配边界的值被汇总，这个基本块对应的支配边界 `DF(DF(B))` 又有分支
    -   因此要求出一个支配边界的闭包 `DF+(B)`，然后在闭包内所有的基本块中插入 \\(\varphi\\)
2.  插入 \\(\varphi\\) 后，进行**重命名**
    -   对 CFG 进行 DFS，并在 DFS 的每个结点中记录每个 `alloca` 对应的值 `IncomingVals[]`
    -   对于遇到的指令进行如下操作：
        -   `alloca`，直接删除
        -   `load`，读取 `IncomingVals[]`
        -   `store` 或者 \\(\varphi\\)，写入 `IncomingVals[]`
    -   遍历完一个基本块后，遍历它的后继，向所有后继的 \\(\varphi\\) 中插入当前基本块流向该后继的边，值为当前结点 `IncomingVals[]` 中的值
    -   假设有多个基本块 `A B` 流入一个基本块 `D`，那么所有值都会在 \\(\varphi\\) 中汇聚
        -   在遍历 `D` 时，需要汇聚的值在 `IncomingVals[]` 中的记录为对应的 \\(\varphi\\)
        -   因此上一步为 \\(\varphi\\) 添加边可以处理所有情况，遍历顺序无关紧要（可以先遍历 `D` 再遍历 `A B`）


## 算法细节 {#算法细节}

这部分代码在 LLVM 的 `PromoteMemoryToRegister.cpp` 这个文件中，对应的 pass 为 `PromoteLegacyPass`。

首先假设我们已经算出了基本块的支配信息。下面描述的 def 一般指 `store` 指令，user 指 `load` 指令。

1.  LLVM 假设所有的局部变量都连续地在函数**入口基本块的头部**使用 `alloca` 进行声明（见函数 `promoteMemoryToRegister()`）
2.  找到这些 `alloca` 指令中那些 promotable 的指令。所谓 promotable，即满足下面的条件：
    -   这个 `alloca` 的 users 中有 `volatile` 指令
    -   这个指令直接用于 `load` 和 `store`（即没有使用过地址，也没有对地址进行计算）
    -   具体看函数 `isAllocaPromotable()` 的判断
3.  分析 `alloca` 的定义使用信息，执行一些优化，（见函数 `PromoteMem2Reg::run()`）
    -   移除没有 users 的 `alloca`
    -   如果一个 `alloca` 只有一个 def，那么 users 可以替换成这个 `store` 的值。这里需要保证下面两个条件（见函数 `rewriteSingleStoreAlloca`）
        -   如果 `load` 和 `store` 在同一个基本块，则 `store` 应该在 `load` 前面
        -   如果二者在不同基本块，则需要保证 `load` 指令能被 `store` 支配
    -   如果某个 `alloca` 的所有 defs 和 users 都在同一个基本块内，且 `store` 在 `load` 前面，则可以将基本块内的 `load` 替换成对应的 `store`
4.  对于每个找到的 `alloca` 指令，在支配边界**放置 \\(\varphi\\) 结点**
    -   计算 `DefBlocks` 的**迭代支配边界**（支配边界闭包），得到要插入的基本块
        -   这里有一个剪枝：只有 `alloca` 是 live-in 的基本块（users 在 def 前面）才可能插入 \\(\varphi\\) 指令（见函数 `ComputeLiveInBlocks()`）
        -   然后对基本块根据序号进行排序，使得插入 \\(\varphi\\) 指令的顺序和编号确定化
    -   在得到的所有支配边界中放置 \\(\varphi\\) 指令
        -   对于同一个 `alloca`，一个基本块内只会插入一个 \\(\varphi\\)
        -   此时指令的操作数还需要下一步进行更新（见函数 `QueuePhiNode()`）
5.  **变量重命名**。整个过程是一个 DFS，为了减小内存开销所以用迭代的方式做
    -   建立一个 map 记录每个 `alloca` 当前对应的值。所有 `alloca` 在函数入口的值都初始化为 `UndefValue`
    -   用迭代 DFS 的方式遍历基本块，基本块信息存在结构体 `RenamePassData` 中，内部包含了一个数组 `Values[]`（即 `IncomingVals[]`）记录当前基本块末尾某个 `alloca` 对应的 `Value`（一次迭代只填入一个前驱流过来的值）
    -   `While (worklist!=NULL)`
        -   标记当前基本块已经处理过，防止重复处理
        -   遍历当前块中**第 4 步添加的** \\(\varphi\\)（程序里原来可能也有 \\(\varphi\\)，不能在这里处理）：
            -   找到 \\(\varphi\\) 对应的 `alloca` `L`
            -   为 \\(\varphi\\) 添加前驱块 `Pred` 到当前块的边（有几条边就要添加几次）：`Phi.add(IncomingVals[L], Pred)`
            -   设置 `IncomingVals[L]=Phi`
        -   如果当前基本块没有重复访问过，则对于基本块内的每条指令
            -   如果当前指令是 `load`，找到对应的 `alloca` `L`，将用到 `load` 结果的地方都替换成 `IncomingVals[L]`
            -   如果当前指令是 `store`，找到对应的 `alloca` `L`，更新版本 `IncomingVals[L]=V` 并删除这条 `store`
    -   将没有访问过的后继基本块加入 `worklist`
6.  收尾：使用 `SimplifyInstruction` 化简 \\(\varphi\\) 指令

在实现简单编译器的时候，可以只做 4、5 两步。


## 简易实现 {#简易实现}

一个简易的实现如下：

<div class="pseudocode">

\begin{algorithm}
  \caption{Promote memory instructions to registers}
  \begin{algorithmic}
    \procedure{Mem2Reg}{$func$}
    \state $allocas \gets$ a set of allocas to be promoted
    \state $allocaDefs \gets$ a dict consisting of alloca and a set of bbs for its corresp. stores
    \state
    \state \comment{\textbf{Stage 1: placing $\phi$s}}
    \state \comment {$newPhis$ is a dict consisting of new $\phi$ and its corresp. alloca}
    \state $newPhis \gets \emptyset$
    \for {$alloca \in allocas$}
      \state set all $bb$s in $func$ to be unvisited
      \state $worklist\_{1} \gets allocaDefs[alloca]$
      \while {$worklist\_{1}$ is not empty}
        \state $bb \gets$ pop an element from $worklist\_{1}$
        \for {$df \in$ dominator frontiers of $bb$}
          \if {$df$ is visited}
            \continue
          \endif
          \state $phi \gets$ new $\phi$ in $bb$
          \state $newPhis[phi] \gets alloca$
          \state add $df$ to $worklist\_{1}$
        \endfor
      \endwhile
    \endfor
    \state
    \state \comment{\textbf{Stage2. Renaming}}
    \state set all $bb$s in $func$ to be unvisited
    \state \comment{$worklist\_{2}$ is dict consisting of bb and its corresp. incoming values}
    \state $worklist\_{2} \gets [($entry $bb$ of $func, )]$
    \while {$worklist\_{2}$ is not empty}
      \state $(bb, incomingVals) \gets $ pop an item from $worklist\_{2}$
      \if {$bb$ is visited}
        \continue
      \endif
      \state set $bb$ to be visited
      \for {$inst \in$ instructions in $bb$}
        \match {type of $inst$}
          \case{alloca}
            \state remove $inst$ from $bb$
          \endcase
          \case{load}
            \if {$allocas$ contains address of $inst$}
              \state replace all use of $inst$ with $incomingVals[\text{address of } inst]$
              \state remove $inst$ from $bb$
            \endif
          \endcase
          \case{store}
            \if {$allocas$ contains address of $inst$}
              \state $incomingVals[\text{address of } inst] \gets$ data of $inst$
              \state remove $inst$ from $bb$
            \endif
          \endcase
          \case{phi}
            \if {$newPhis$ contains $inst$}
              \state $alloca \gets newPhis[inst]$
              \state $incomingVals[alloca] \gets inst$
            \endif
          \endcase
        \endmatch
        \state \comment{update $\phi$ in successors of $bb$}
        \for {$succ \in$ succs of $bb$}
          \state add $(succ, incomingVals)$ to $worklist\_{2}$
          \for {$phi \in \phi$ in $succ$}
            \if {keys of $newPhis$ contains $phi$}
              \state $alloca \gets newPhis[phi]$
              \state add operand $(incomingVals[alloca], bb)$ to $phi$
            \endif
          \endfor
        \endfor
      \endfor
    \endwhile
    \endprocedure
  \end{algorithmic}
\end{algorithm}

</div>
