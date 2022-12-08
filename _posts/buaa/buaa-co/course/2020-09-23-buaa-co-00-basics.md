---
layout: "post"
title: "「BUAA-CO」 00 基础认识"
subtitle: "摩尔定律，并行性，硬件构成，层次结构"
author: "roife"
date: 2020-09-23

tags: ["北航计组@课程相关", "课程相关@Tags", "Digital Design and Computer Architecture@读书笔记", "读书笔记@Tags", "体系结构@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 重要认识

## 摩尔定律

集成电路上可以容纳的晶体管数目在大约每经过 24 个月便会增加一倍，即处理器的性能每隔两年翻一倍。

## 局部性原理

指 CPU 访问存储器时，无论是存取指令还是存取数据，所访问的存储单元都趋于聚集在一个较小的连续区域中。

局部性原理决定了计算机的存储结构设计。

## Amdahl's law

使用并行处理的提速由问题的可并行的部分决定，被必须串行的部分限制。$S=1/(1 - a + \frac{a}{n})$，其中 $a$ 表示可并行部分，$n$ 表示并行处理器数量，$S$ 表示提速。

# 计算机基本硬件构成

- CPU（Multicore）
  + 数据通路（ALU + PC + Reg）：计算与存储
  + 控制器：执行指令
  + Cache
  + MMU（内存管理）
- 主存储器（内存）
- 输入输出设备
  + 硬盘（SATA/etc）
  + USB
  + PCI 总线
  + PCI-E 总线

# 计算机层次结构

硬件部分：晶体管 → 数字电路 → 微架构（数据通路+控制器）→ CPU + 存储 + I/O

软件部分：操作系统 + 编译器/汇编器 + 应用软件

硬件与软件部分依靠指令集沟通。
