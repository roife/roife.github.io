---
layout: "post"
title: "「BUAA-OS-Lab」 Lab2-2 虚拟内存管理"
subtitle: "虚拟内存管理"
author: "roife"
date: 2021-04-13

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "C@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 课上

## Exam

主要考察**自映射**内容。

以下题目中如果要定义新的函数，需要在 `include/pmap.h` 中添加对应的声明。

在 `mm/pmap.c` 中添加函数声明：

```c
u_long cal_page(int func, u_long va, int n, Pde *pgdir);
```

其中 `func` 为 0～3，对应 4 个 tasks。

### Task 0

#### 题目

一个 64 位系统使用三级页表，页表大小为 4KB，且页表字对齐，求 64 位中虚拟地址位数。
函数直接返回答案。

#### 分析

64 位系统中，一个字为 8Byte，则一级页目录中有 $2^9$ 项（因为一个页表 4KB，那么 $2^9 * 8 = 4K$），即每级页目录需要 9 位。

所以总共为 $9*3 + 12 = 39$ 位。

需要注意的一个点是，这里虚拟空间地址只有 $2^{39}$，并没有完全利用 $2^{64}$。

### Task 1

#### 题目

给出二级页表的起始虚拟地址 `va`，返回页目录的起始地址。

#### 分析

`va` 对应的页表是第 `va >> 12` 项。每个页表项占用 32 位（4 字节），即偏移地址为 `(va >> 12) * 4`。

所以答案是 `va + ((va >> 12) << 2)`。

```c
return va + ((va >> 12) << 2);
```

### Task 2

#### 题目

给出页目录所在虚拟地址 `va` 和一个整数 `n`，返回页目录第 `n` 项对应的二级页表的起始虚拟地址。

#### 分析

考虑虚拟地址结构：

|页目录|页表|页内偏移|
|-|-|-|
| 10 位 | 10 位 | 12 位 |

由于是自映射，所以页目录和所有页表放在同一个 4MB 的空间中。所以：
- 地址中的高 10 位和页目录相同（放在一起了）
- 一个页表为 4KB，那么第 $n$ 项就是 $4KB * n$
- 因为问的是页表的起始虚拟地址，所以页内偏移为 0

```c
return (va & 0xFFC00000) + (n << 12);
```

### Task 3

#### 题目

给出一级页表地址 `pgdir` 和二级页表起始地址 `va`。在页目录中装载对应的项，并加上权限位，使得其能够完成自映射。
函数返回 `0`。

#### 分析

`PDX(va)` 表示首个二级页表对应第几项页目录，所以地址为 `pgdir + PDX(va)`。

该页目录项存的是所在页表的地址，即 `PADDR(pgdir)`。

> 理论上页表应该在一个 4M 对齐的内存中，所以写 `Pde *pgdir_entryp = pgdir + PDX(pgdir);` 也可以，但是不对，需要询问一下

```c
Pde *pgdir_entryp = pgdir + PDX(va);
*pgdir_entryp = (PADDR(pgdir)) | PTE_V;
return 0;
```

## Extra

在 `mm/pmap.c` 中添加函数声明：

```c
int count_page(Pde *pgdir, int *cnt);
```

### 题目

给出页目录地址 `pgdir`。填充一个数组 `cnt`，使得 `cnt[i]` 表示第 `i` 个物理页被引用了多少次。

提示：
- 每个物理页可能被多个虚拟页引用
- `cnt` 的初始值可能初始不是 `0`
- 包括页目录、二级页表以及被引用的物理页

### 分析

注意，Extra 没有自映射！做题不要带着惯性，如果以为还是自映射，就会以为在算物理页的时候，页目录、二级页表已经算进去了（实际上没有），最终导致漏算。

```c
int count_page(Pde *pgdir, int *cnt) {
    int i;
    for (i = 0; i < npage; i++) cnt[i] = 0;

    ++cnt[PPN(PADDR(pgdir))];

    for (i = 0; i < 1024; ++i) {
        Pde *pgdir_entryp = pgdir + i;

        if((*pgdir_entryp) & PTE_V) {
            ++cnt[PPN(*pgdir_entryp)];

            Pte *pgtable = KADDR(PTE_ADDR(*pgdir_entryp));

            int j;
            for (j = 0; j < 1024; ++j) {
                Pte *pgtable_entryp = pgtable + j;
                if((*pgtable_entryp) & PTE_V) ++cnt[PPN(*pgtable_entryp)];
            }
        }
    }
    return npage;
}
```

## 感想

体验极差。

Task 0 不会算，然后评测的时候 Task0 不对直接 0 分，很搞心态。

后来枚举 Task 0 的值做出来了。