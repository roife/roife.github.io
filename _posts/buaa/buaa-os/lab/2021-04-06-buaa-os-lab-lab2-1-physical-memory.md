---
layout: "post"
title: "「BUAA-OS-Lab」 Lab2-1 物理内存管理"
subtitle: "物理内存管理"
author: "roife"
date: 2021-04-06

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "C@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 课上

课下的时候一定要多读读代码，熟悉一些宏和函数，方便课上使用。

## Exam

以下题目中如果要定义新的函数，需要在 `include/pmap.h` 中添加对应的声明。

### Task 1

#### 题目

在 `mm/pmap.c` 中新增一个函数 `int page_alloc2(struct Page **)`，其效果和 `page_alloc` 相同，但是会输出当前申请页面的页号和物理地址。

#### 分析

直接调用原来的 `page_alloc`，然后课下的时候注意 `page2ppn` 和 `page2pa` 两个宏（函数）的用法即可。

注意传入的参数类型是 `struct Page *`，所以应该用 `*pp`。

```c
int page_alloc2(struct Page **pp) {
    page_alloc(pp);
    printf("page number is %x, start from pa %x\n", page2ppn(*pp), page2pa(*pp));
    return 0;
}
```

### Task 2

#### 题目

在 `mm/pmap.c` 中新增一个函数 `void get_page_status(int)`，传入一个物理地址，输出询问次数和页面的状态 `times:%d, page status:%d\n`：
- 如果页面空闲，即没有被分配，则输出 `3`
- 如果页面被分配，但是没有被使用，则输出 `2`
- 如果页面被分配，而且正在被使用，则输出 `1`

#### 分析

直接用 `LIST_FOREACH` 遍历列表，看目前询问的页面在不在链表之中。

注意使用 `pa2page` 宏来将物理地址转换成对应的页面。

```c
void get_page_status(int pa) {
    static int kase; // 也可以在函数外面定义 int kase = 0;
    ++kase;

    struct Page *pp = pa2page(pa);

    int is_free = 0;

    struct Page *page_i;
    LIST_FOREACH(page_i, &page_free_list, pp_link) {
        if(page_i == pp) {
            is_free = 1;
            break;
        }
    }

    int status;
    if(is_free) status = 3;
    else if (pp->pp_ref == 0) status = 2;
    else status = 1;

    printf("times:%d, page status:%d\n", kase, status);
}
```

## Extra

这次的 Extra 要求使用位图来管理页面分配，下面的所有题目都不能用链表！

位图，即 bitmap，是一个整型数组，数组中整型的每一位代表一个页面是否被分配：如果为 `1` 则是已经被分配，`0` 则是没有。

例如对于 `0` 号页面而言，对应的是 `bitmap[0]` 的第 `0` 位；对于 `63` 号页面而言，对应的是 `bitmap[1]` 的第 `31` 位。例如如果只有 `63` 被分配了，那么 `bitmap[1]` 为 `0x80000000`。

同样，下面定义的函数需要在 `include/pmap.c` 中声明

### Task 1

#### 题目

在 `mm/pmap.c` 中定义 `unsigned int page_bitmap[NUM]`，其中 `NUM` 恰好所需要的位图宽度（不能多也不能少）。

并且编写 `void page_init(void)` 函数，初始化位图，并且输出 `NUM`。

#### 分析

首先是 `NUM` 的计算。课下已经知道内存大小为 64MB，单个页大小为 4KB，则总共有 `(64 * 1024 * 1024) / (4 * 1024)` 个页面，又由于 `int` 可以表示 32 个页面的分配情况，则 $\mathrm{NUM} = (64 * 1024 * 1024) / (4 * 1024) / 32 = 512$。

`page_init` 的编写和课下差不多，先初始化 `page_bitmap`。然后将已经用的内存引用 `pp_ref` 设置为 `1`，并且标记为已经被申请；没用的内存引用设置为 `0`。

为了简化代码，这里定义了两个辅助函数：
- `int bitmap_get(int pn)`：获取 `pn` 对应位的值
- `void bitmap_set(int pn, int k)`：设置 `pn` 对应位的值为 `k`

```c
inline int bitmap_get(int pn) { return page_bitmap[pn / 32] & (1 << (pn % 32)); }
inline void bitmap_set(int pn, int k) {
    if (k == 0) page_bitmap[pn / 32] &= (~(1 << (pn % 32)));
    else page_bitmap[pn / 32] |= (1 << (pn % 32));
}
```

```c
#define NUM 512
unsigned int page_bitmap[NUM];

// ...

void page_init(void) {
    // 清空位图标记
    int i;
    for (i = 0; i < NUM; ++i) page_bitmap[i] = 0;

    // 计算空闲内存地址
    freemem = ROUND(freemem, BY2PG);

    // 计算已用空间
    int size = PADDR(freemem) / BY2PG;

    // 标记已用空间
    for (i = 0; i < size; ++i) {
        pages[i].pp_ref = 1;
        bitmap_set(i, 1);
    }

    // 清空空闲内存
    for (; i < npage; ++i) {
        pages[i].pp_ref = 0;
    }

    printf("page bitmap size is %x\n", NUM);
}
```

### Task 2

#### 题目

如上，编写 `int page_alloc(struct Page **pp)` 申请页面，要求返回的页面应该是空闲页面中编号最小的页。

#### 分析

```c
int page_alloc(struct Page **pp) {
    // 查找空闲页面
    int i, pos = -1;
    for (i = 0; i < NUM; ++i) {
        if (page_bitmap[i] != 0xFFFFFFFF) {
            pos = i;
            break;
        }
    }

    // 如果没有空闲页面，则返回错误
    if (pos == -1) return -E_NO_MEM;

    int page_no = pos * 32;
    while(bitmap_get(page_no)) ++page_no;

    struct Page *ppage_temp = &(pages[page_no]);
    // 清空页面内容
    bzero((void*)page2kva(ppage_temp), BY2PG);
    // 标记已经被申请
    bitmap_set(page_no, 1);

    *pp = ppage_temp;

    return 0;
}
```

下面还有一种更简洁的方法（但是很慢）：

```c
// 直接遍历页面，最简洁，但是更慢
int page_alloc(struct Page **pp) {
    int page_no;
    for (page_no = 0; page_no < npage; ++i) {
        if (bitmap_get(page_no) == 0) {
            struct Page *ppage_temp = &(pages[page_no]);
            // 清空页面内容
            bzero((void*)page2kva(ppage_temp), BY2PG);
            // 标记页面空闲
            bitmap_set(page_no, 1);

            *pp = ppage_temp;
            return 0;
        }
    }

    // 找不到空闲页面
    return -E_NO_MEM;
}
```

### Task 3

#### 题目

如上，编写 `void page_free(struct Page **)` 释放页面。

#### 分析

```c
void page_free(struct Page *pp) {
    if (pp->pp_ref > 0) return;
    if (pp->pp_ref == 0) {
        bitmap_set(page2ppn(pp), 0);
        return;
    }
    panic("cgh:pp->pp_ref is less than zero\n");
}
```