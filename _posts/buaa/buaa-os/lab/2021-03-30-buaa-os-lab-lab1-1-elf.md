---
layout: "post"
title: "「BUAA-OS-Lab」 Lab1-1 ELF"
subtitle: "ELF 文件解析"
author: "roife"
date: 2021-03-30

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "Linux@Tags", "C@编程语言", "ELF@Linux"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 课上

## Exam

### 题目

类似于课下，但是改为输出 ELF 文件的 Segment Table（Program Header Table）中各个 segment 对应的段偏移 `p_offset` 和对齐方式 `p_align` 信息，输出格式为格式为 `%d:0x%x,0x%x\n`。

### 分析

```c
Elf32_Phdr *phdr = NULL;

u_char *ptr_ph_table = NULL;
Elf32_Half ph_entry_count;
Elf32_Half ph_entry_size;

if (size < 4 || !is_elf_format(binary)) {
    printf("not a standard elf format\n");
    return 0;
}

ptr_ph_table = binary + ehdr->e_phoff;
ph_entry_count = ehdr->e_phnum;
ph_entry_size = ehdr->e_phentsize;

for (Nr = 0; Nr < ph_entry_count; ++Nr) {
    phdr = (Elf32_Phdr*)(ptr_ph_table + ph_entry_size * Nr);
    printf("%d:0x%x,0x%x\n", Nr, phdr->p_offset, phdr->p_align);
}
```

## Extra

### 题目

大端和小端是文件存储的两种不同方式。在一个字中，如果高字节存储在低地址中则是大端；反之，如果低字节存储在高地址中则是小端。例如一个字 `0x12345678` 存在 `0x0000`～`0x0003` 中，则二者存储方式如下：

| 地址 | `0x0000` | `0x0001` | `0x0002` | `0x0003` |
|-|-|-|-|-|
| 大端 | `0x12` | `0x34` | `0x56` | `0x78` |
| 小端 | `0x78` | `0x56` | `0x34` | `0x12` |

题目要求首先判断文件是大端还是小端。如果是大端，输出 Section Table 中各个 section 的 `sh_addr`，格式同课下；如果是小端，则输出 Segment Table 中各个 segment 的 `p_filesz` 和 `p_memsz`，并用小端的形式输出，格式同 exam。

大小端可以根据 ELF 中头信息的第五位 `e_ident[5]` 判断，如果是 1 那么就是小端文件，否则是大端文件。

### 分析

需要注意的是对于大端文件，每次读取的时候都要反转字节，并且反转的时候要注意对应的数据类型长度是一个字还是半个字。

```c
#include "kerelf.h"
#include <stdio.h>
#define EI_DATA 5

int is_elf_format(u_char *binary)
{
        Elf32_Ehdr *ehdr = (Elf32_Ehdr *)binary;
        if (ehdr->e_ident[EI_MAG0] == ELFMAG0 &&
                ehdr->e_ident[EI_MAG1] == ELFMAG1 &&
                ehdr->e_ident[EI_MAG2] == ELFMAG2 &&
                ehdr->e_ident[EI_MAG3] == ELFMAG3) {
                return 1;
        }

        return 0;
}

Elf32_Half reverseHalf(Elf32_Half x) {
    return (x << 8) + ((x >> 8) & 0x00FF);
}

Elf32_Word reverseWord(Elf32_Word x) {
    return (x << 24) + ((x << 8) & 0x00FF0000) + ((x >> 8) & 0x0000FF00) + (x >> 24);
}

int readelf(u_char *binary, int size)
{
    Elf32_Ehdr *ehdr = (Elf32_Ehdr *)binary;

    // check whether `binary` is a ELF file.
    if (size < 4 || !is_elf_format(binary)) {
            printf("not a standard elf format\n");
            return 0;
    }

    if (ehdr->e_ident[EI_DATA] == 1) {
        // Little End
        int Nr;

        Elf32_Phdr *phdr = NULL;

        u_char *ptr_ph_table = NULL;
        Elf32_Half ph_entry_count;
        Elf32_Half ph_entry_size;

        ptr_ph_table = binary + ehdr->e_phoff;
        ph_entry_count = ehdr->e_phnum;
        ph_entry_size = ehdr->e_phentsize;

        for (Nr = 0; Nr < ph_entry_count; ++Nr) {
            phdr = (Elf32_Phdr*)(ptr_ph_table + ph_entry_size * Nr);
            printf("%d:0x%x,0x%x\n", Nr, phdr->p_filesz, phdr->p_memsz);
        }
    } else {
        // Big End
        int Nr;

        Elf32_Shdr *shdr = NULL;

        u_char *ptr_sh_table = NULL;
        Elf32_Half sh_entry_count;
        Elf32_Half sh_entry_size;

        // 注意读出的偏移信息、数量、大小都要反转
        ptr_sh_table = binary + reverseWord(ehdr->e_shoff);
        sh_entry_count = reverseHalf(ehdr->e_shnum);
        sh_entry_size = reverseHalf(ehdr->e_shentsize);

        for (Nr = 0; Nr < sh_entry_count; ++Nr) {
            shdr = (Elf32_Shdr*)(ptr_sh_table + sh_entry_size * Nr);
            printf("%d:0x%x\n", Nr, reverseWord(shdr->sh_addr));
        }
    }
    return 0;
}
```
