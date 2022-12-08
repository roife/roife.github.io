---
layout: "post"
title: "「BUAA-CO」 09 存储系统"
subtitle: "Cache，VM，磁盘和CD"
author: "roife"
date: 2021-01-17
tags: ["北航计算机组成理论@课程相关", "课程相关@Tags", "Digital Design and Computer Architecture@读书笔记", "读书笔记@Tags", "体系结构@Tags", "集成电路@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 存储器性能分析

$$MissRate = \frac{misses}{TotalMemoryAccess} = 1 - HitRate$$

$$HitRate = \frac{hits}{TotalMemoryAccess} = 1 - MissRate$$

$$AMAT = t_{cache} + MR_{cache} (t_{MM} + MR_{MM} t_{VM})$$

查找数据时，处理器会先在 Cache 中找，如果找不到则到主存中找，如果还是找不到则到 VM 中找。

# 存储层次

$$Registers \rightarrow L1\$ \rightarrow L2\$ \rightarrow MainMemory \rightarrow SecondaryMemory(Disks)$$

# 高速缓存 Cache

## Cache 介绍

Cache 会用一个小容量的高速存储器保存最近访问过的内容，以便加速以后的访问速度。Cache 的依据为计算机的时间局限性（刚刚用过的数据可能马上又会用到）和空间局限性（刚刚用过的数据周围的数据可能马上会被用到）。Cache 使用 SRAM 构建，速度更快，但是密度更低，成本更高，更加耗能；而主存使用 DRAM 构建。一般会使用 `$` 表示 Cache（谐音）。

计算机访问数据时会先在 Cache 中查找，如果找到了则称为 Hit，否则称为 Miss。如果 Miss 了则需要将新的数据放入 Cache。

注意，Cache 上的一块不一定只对应一个字或者字节。

在 Cache 中一般用 MR（Miss Rate）和 MP（Miss Penalty）衡量性能。

## Cache 类型

下面假设 Cache 的容量为 $C$，组数为 $S$，块大小为 $b$，总块数为 $B$，路数 $N$。

一个 Cache 可以分为 S 组，数据可以映射到对应组中的任意一块：
- 直接映射 Cache：$S = B$，每组 $1$ 块
- N 路组相联 Cache：$S = B / N$，每组 $N$ 块
- 全相联 Cache：$S = 1$，每组 $B$ 块

### Cache 地址结构

主存地址地址会被分为 3 部分：
- $Offset = \log b$：表示块内部的索引
- $Index = \log S$：映射到 Cache 的哪一块（可能有多块主存映射到同一块 Cache），相当于一个 Hash Function
- $Tag = A - I - O$：用来标识当前某一块 Cache 属于主存的哪一块

Cache 可以看成对主存进行分区，每个区域的大小为 Cache 的大小。其中 `Index` 可以看作区内块编号，`Tag` 可以看作区编号。`Index` 相同则会被映射到同一块 Cache 上。关联度越大，`Tag` 位越长（全相联最大），`Index` 位越小。

![cache-memory-address-field](/img/in-post/post-buaa-co/cache-memory-address-field.png){:height="350px" width="350px"}

一般 Cache 的一块会由数据，Tag 位和 Valid 位构成。其中 Valid 位用来标记当前这一位是否可用（比如刚开机，则所有的行里面的都是假数据）。

$$TotalBits = \#raws \times (b + T + 1)$$

### 直接映射 Cache

在直接映射 Cache 中，第 $i$ 块地址被映射到 $i \bmod B$ 组上。每一组只有一块。
- $Offset = \log b$
- $Index = \log (B)$
- $Tag = A - I - O$

![direct-mapped-cache-internal](/img/in-post/post-buaa-co/direct-mapped-cache-internal.png)

#### 直接映射 Cache 的控制器

一个直接映射 Cache 需要考虑四种情况：
- 读命中：直接从块中读取需要的字
- 写命中：直接向块中写入需要的字
- 读缺失：通知 CPU 暂停，然后写回 Cache 中的块，再从主存中载入相应的块，通知 CPU 继续执行
- 写缺失：先执行读缺失的步骤，然后向 Cache 中写入数据（可以在载入块时直接替换要写入的字）

直接映射 Cache 的控制器可以看作一个状态机，状态转移图如下。

![direct-mapped-cache-controller](/img/in-post/post-buaa-co/direct-mapped-cache-controller.png){:height="600px" width="600px"}

### 多路组相联 Cache

在组相联 Cache 中，每一块主存依然映射到某一组中，但是每一组有多个块，它可以映射到组内任意一个块中。
读写操作可以在同一组的所有块中并行进行。
- $Offset = \log b$
- $Index = \log (B/N)$
- $Tag = A - I - O$

![set-associative-cache](/img/in-post/post-buaa-co/set-associative-cache.png)

### 全相联 Cache

全相联 Cache 类似于多路组相联 Cache，其整一个 Cache 就是一组，主存可以映射到 Cache 的任意一块上。但是这样会造成比较电路膨胀。

## Cache 的替换策略

在直接映射 Cache 中，新 Cache 可以直接替换旧 Cache，但是在多路组相联 Cache 和全相联 Cache 中则有多种替换算法。

最简单的思路是直接随机替换。常用的算法是使用 LRU（Least Recently Used）算法。LRU 算法会自动替换掉最少使用的那一块，这样使得 Cache 电路更加复杂。

## Cache 的读写策略

读取 Cache miss 时有两种方案：
- 读通过（Read through）：直接从内存中读取数据
- 读分配（Read allocate）：先把数据读取到 Cache 中，再从 Cache 中读数据

当 Hit 时，有两种写入方案：
- 写通过（Write-through）：写 Cache 的同时写主存，效率较低
- 写回（Write-back）：写操作只更新 Cache 中的数据，直到 Block 替换时才把整个 Block 写回主存。一般会用一个 Dirty Bit 标记是否修改过。更加常用

当 Miss 时，也有两种方案：
- 写分配（Write allocate）：先把要写的数据载入到 Cache 中，写 Cache，然后再将 Cache 写回去
- 非写分配（No write allocate）：直接把要写的数据写入到内存中

## 多级 Cache

现代处理器一般会使用多级 Cache，即 L1 ~ L3，速度以此减小，容量逐渐增大。

其中，L1 会区分指令 Cache（Instructions Cache）和数据 Cache（Data Cache）（哈弗架构）。

多级 Cache 的平均访问时间 $AMAT = L1 HT + L1 MR × (L2 HT + L2 MR × L2 MP)$，依次类推。

同时定义两种 Miss Rate。LMR 表示当前 Cache 缺失率，GMR 表示整个 Cache 缺失率。可以发现 $GMR \leq LMR$。

$$L2\$\ local\ MR = \frac{L2\$\ misses}{L1\$\ misses}$$

$$Global\ MR = L1\$\ misses \times \cdots Ln\$\ misses$$

由于主存访问比 Cache 慢很多，所以一般 L1 重点在于减少 Hit 时间（比如通过变得更小），而 L2/L3 重点在于减小 MR（例如变得更大）。

## Cache 性能及改进

$$AMAT = HT + MR × MP$$

Cache 变大能减小 MR，但是会增加 HT。

$$CPU\ Time = IC (Instructions) × CPI_{stall} × CC (Clock\ Cycle\ Time)$$

$$CPI_{stall} = CPI_{base} + \frac{Accesses}{IC} \times MR \times MP$$

# 虚拟存储器 VM

## VM 介绍

由于程序运行的数据在主存中放不下，而且两个程序共用内存会互相干扰，所以我们让程序运行在各自独立的虚拟地址空间中，而不是真实的物理地址空间，称为存储器保护（memory protection）。从虚拟地址空间到物理地址空间存在一个映射关系。

VM 和 PM 被分为多个页（Page），相当于 Cache 中的块。虚页有可能在 DRAM 中，也有可能在硬盘上。注意，虚拟地址空间往往比物理地址空间（主存空间）大，所以大部分数据存在硬盘上（称为交换空间，swap space）。

VM 相当于一个全相联 Cache。在页式虚拟存储器中，当程序要使用某个页时，先根据提供的虚拟地址查找页表，得到对应的物理地址，如果对应的页在主存中则调用，否则将其载入后调用。

![vm](/img/in-post/post-buaa-co/vm.png){:height="400px" width="400px"}

## 地址

在 VM 中，虚拟地址和物理地址都被分为两部分：虚页号（VPN）+ 页内偏移（offset），或者物理页号（PPN）+ 页内偏移（offset）。
规定虚拟地址和物理地址的页内偏移相同。

- $Offset = \log PageSize$
- $VPN = VA - Offset$
- $PPN = PA - Offset$

![vm-vpn-ppn](/img/in-post/post-buaa-co/vm-vpn-ppn.png)

## 页表

页表记录了 VPN 和 PPN 的映射关系。对于每一个虚页，页表中包含了一项记录对应的 PPN 和 Valid 位。除此之外，页表还有可能保存对应虚页的读写权限。查找时页表类似于一个数组，根据虚页号找到对应的位置即可获取信息。

由于页表一般比较大，所以存在主存中。页表可以放在主存中的任意位置，操作系统根据一个专用的寄存器“页表寄存器（page table register）”来获取页表存储的初始位置。

![vm-page-table](/img/in-post/post-buaa-co/vm-page-table.png)

## TLB

由于 VM 的存在，每次读写数据时需要读取两次主存：先查找页表，然后根据页表提供的 PA 找主存中的数据。所以处理器会将页表中的一部分保存在一个**专用的小型 Cache **中，叫做转换后备缓冲器（translation lookaside buffer，TLB）。即 TLB 是页表的 Cache。

![vm-tlb-cache](/img/in-post/post-buaa-co/vm-tlb-cache.png){:height="400px" width="400px"}

注意使用了 TLB 后会直接使用 TLB 进行地址转换，如果 TLB 中找不到，则先将页表在于 TLB 再进行转换。

![vm-tlb-1](/img/in-post/post-buaa-co/vm-tlb-1.png){:height="500px" width="500px"}

使用了 TLB 后的 CPU 结构如下：

![vm-tlb-cpu](/img/in-post/post-buaa-co/vm-tlb-cpu.png)

TLB 使用全相联的 Cache，而且比较小，所以访问时间足够快。使用了 TLE 后，原来读取数据需要访问两次主存，现在最少可以只访问一次。TLB 和 Cache 类似，由 Valid 位，Tag 位（VPN）和 PPN 等组成，和 Cache 类似。

![vm-tlb-translation](/img/in-post/post-buaa-co/vm-tlb-translation.png)

## 替换策略

VM 的替换策略类似于 Cache。而且由于硬盘比主存慢很多，所以一般使用写回和 LRU 算法进行替换。

## 多级页表

页表有可能会很大，所以有可能会使用多级页表。

例如在二级页表中，会再次对 VPN 进行划分为页表号（page table number）和页表偏移量（page table offset）。页表会分成多个子页表，编号为页表号，页表偏移量为该子页表内对应的项编号。其中一级页表存储每个子页表在的地址，同时有一个 Valid 标记是否可用。

![vm-two-level-page-table](/img/in-post/post-buaa-co/vm-two-level-page-table.png)

## VM 性能及改进

$$AMAT_{paging} = AMAT_{no-paging} + MR_{cache} \times MR_{mem} \times t_{disk}$$

改进方法：
- 使用多级 TLB
- 使用变长页表

# 存储器阵列

## 概述

一个 $N$ 位地址和 $M$ 位数据的阵列有 $2^N$ 行和 $M$ 列，每行称为一个字。

![通用存储器阵列](/img/in-post/post-buaa-co/generic-memory-array.png "generic-memory-array"){:height="200px" width="200px"}

### 位单元

存储器由位单元（bit cell）组成，每个位单元存储了一位数据。

每个位单元和字线（wordline）以及位线（bitline）相连。字线用于控制写入和读取状态，位线用于存储数据。

读取时，将位线置于浮空值，字线置于高电平，让位单元驱动位线；写入时，将位线置于写入值，字线置于高电平，使得值被写入。

### 存储器

存储器由译码器和位单元组成，其中译码器用来控制字线读取数据。

![存储器阵列](/img/in-post/post-buaa-co/memory-array.png "memory-array"){:height="700px" width="700px"}

存储器可以有多个端口进行读写操作，如图有两个读端口和一个写端口，地址分别从 $A1 ~ A3$ 读入。

![存储器端口](/img/in-post/post-buaa-co/memory-ports.png "memory-ports"){:height="200px" width="200px"}

存储器可以分为 RAM（Random Access Memory）和 ROM（Read Only Meomory）。二者区别在于数据是否是易失的。

RAM 可以分为 DRAM 和 SRAM，前者利用电容充放电，后者利用交叉耦合反相器。

## RAM

### DRAM

DRAM 利用电容充放电存储数据，并且使用 nMOS 作为开关。

电容充电到 $V_{DD}$ 时值为 $1$，放电到 $GND$ 时值为 $0$。

![DRAM](/img/in-post/post-buaa-co/dram.png "DRAM"){:height="200px" width="200px"}

读取时，数据从电容传输到位线；写入时，数据从位线传输到电容。由于读取会破坏电容的状态，因此每次读取都必须进行一次重写。

由于电容会慢慢漏电，所以必须几 ms 刷新一次（读出后再重写）。

### SRAM

SRAM 将数据存储在反相器中，不需要进行刷新操作。读写时两个 nMOS 同时打开。

![SRAM](/img/in-post/post-buaa-co/sram.png "SRAM"){:height="250px" width="250px"}

如果噪声干扰了 SRAM 的值，反相器可以自动恢复。

数字系统中会利用小型 SRAM 来存储临时变量，这种电路比触发器阵列更加紧凑。其电路符号和存储器相同。

如果要写入，字线变为高电平，两条位线的其中一条变为高电平，取决于要写入的数据。读取时，字线变为高电平，数据从位线读出。

### 比较触发器/DRAM/SRAM

| 存储器类型 | 晶体管数 | 延迟 |
|------------|----------|------|
| 触发器     | ~20      | 快   |
| SRAM       | 6        | 中等 |
| DRAM       | 1        | 慢   |

DRAM 由于读取后需要刷新值，因此吞吐量较低。新技术如 DRAM（SDRAM）和（DDR）SDRAM 已经克服了这些问题。SDRAM 使用时钟使得寄存器访问流水线化，DDR 则同时使用时钟的上升沿和下降沿访问寄存器。

## ROM

ROM 用晶体管的存在与否来存储位。

![ROM](/img/in-post/post-buaa-co/rom-bit-cell.png "rom-bit-cell"){:height="250px" width="250px"}

读取时，位线被缓慢拉伸至 $1$，然后打开字线，如果此处有晶体管（接地）则位线变为低电平，否则将保持高电平。
因此 ROM 可以用 “点表示法” 来描述，有点的地方代表此位为 $1$。

![ROM 点表示法](/img/in-post/post-buaa-co/rom-dot-notation.png "rom-dot-notation"){:height="500px" width="500px"}

ROM 还可以看成是由 AND 和 OR 门电路组合而成的逻辑。其中 AND 门形成一个译码器，OR 门对数据进行选择，让字线直接驱动位线。

![门电路 ROM](/img/in-post/post-buaa-co/rom-gate.png "rom-gate"){:height="300px" width="300px"}

### 可编程 ROM

可编程 ROM 分为一次可编程 ROM 和可重复编程 ROM。

一次可编程 ROM 也称熔丝烧断可编程 ROM，通过选择性熔断熔丝来进行编程。当熔丝存在时，晶体管接地，即值为 $0$，否则为 $1$。

![熔丝熔断可编程 ROM](/img/in-post/post-buaa-co/fuse-programmable-rom.png "fuse-programmable-rom"){:height="250px" width="250px"}

可重复编程 ROM 分为可擦除 PROM（Erasable PROM，EPROM），电子可擦除 ROM（Electrically Erasable PROM，EEPROM）和闪存。

EPROM 使用浮动栅晶体管代替 nMOS 和熔丝，不需要物理连接。对其使用高电平时，可以产生绝缘体到浮动栅的电子沟道，使晶体管开启并连接位线到字线。而当期暴露在强烈紫外线半小时后，电子会从浮动栅移走，从而关闭晶体管。

EEPROM 和闪存原理类似，由电路进行擦除，不需要紫外线，并且可以对单元进行单独擦除。

### ROM 实现查找表

ROM 可以用于实现组合逻辑的功能，这样的存储阵列称为查找表（Lookable Table，LUT）。（因为 ROM 本身可以表示为 AND 和 OR 构建的门电路）

![ROM 实现查找表](/img/in-post/post-buaa-co/memory-array-as-lookup-table.png "memory-array-as-lookup-table"){:height="400px" width="400px"}

## HDL 实现存储器

### RAM

```verilog
reg [M-1 : 0] mem [2**N-1 : 0];

always @(posedge clk)
    if (we)     mem[adr] <= cin;

assign dout = mem[adr];
```

### ROM

```verilog
always @(*)
    case (adr)
        2'b00:  dout <= 3'b011;
        2'b01:  dout <= 3'b110;
        2'b10:  dout <= 3'b100;
        2'b11:  dout <= 3'b010;
    endcase
```

## 存储芯片结构

### SRAM

对于 $m*n$ 的 SRAM 芯片，最终存储矩阵为 $\frac{\log_2 mn}{2} * \frac{\log_2 mn}{2}$。

![4096*4 SRAM](/img/in-post/post-buaa-co/sram-1.png){:height="500px" width="500px"}

### DRAM

DRAM 在存储中使用行列地址管脚复用的形式，即行列使用同一个管脚，分时发送信号。
对于 $m*n$ 的芯片，最终存储矩阵为 $\frac{\log_2 m}{2} * \frac{\log_2 m}{2}$。

![2048*4 DRAM](/img/in-post/post-buaa-co/dram-1.png){:height="500px" width="500px"}

DRAM 一次刷新一行，因此刷新周期由行数决定。每次刷新会由一个 timer 和 counter 决定。

![DRAM-2](/img/in-post/post-buaa-co/dram-2.png)

## 存储器扩展

指用小的芯片模拟出大的芯片，如用 4 块 1K\*4 模拟出 1 块 2K\*8。

芯片扩展分为两种：字扩展和位扩展。
- 字扩展：扩大地址范围，如 $1K \rightarrow 2K$，地址高位用作片选信号
- 位扩展：扩展一个地址的数据大小，如 $4 \rightarrow 8$，多块芯片并联连接

![storage-expansion](/img/in-post/post-buaa-co/storage-expansion.png){:height="500px" width="500px"}

# 逻辑阵列

逻辑阵列类似于存储阵列，可以对门电路进行编程，分为可编程逻辑阵列（Programmable Logic Array，PLA）和现场可编程逻辑门阵列（Field Programmable Gate Array，FPGA）。前者只能实现两级组合逻辑，后者可以实现多级组合逻辑和时序逻辑，并且集成了 I/O，RAM 阵列等功能。

## PLA

PLA 使用 SOP 的方式实现逻辑，输入驱动 AND 阵列，产生的蕴含项再驱动 OR 阵列。

![3\*3\*2 位 pla](/img/in-post/post-buaa-co/3-3-2-bit-pla.png "3-3-2-bit-pla"){:height="500px" width="500px"}

ROM 可以看作特殊的 PLA，区别在于 ROM 的蕴含项总是 $2^N$ 的，而 PLA 不一定。

## FPGA

FPGA 是一个可配置逻辑元件（Logic Element，LE）阵列，也称为可配置逻辑单元（Configurable Logic Bloc，CLB）。每个 LE 都可以实现组合或时序逻辑功能。多个 LE 组成了一个逻辑阵列单元（Logic Array Block，LAB）。

LE 被输入/输出元件（I/O Element，IOE）包围。IOE 将 LE 和芯片管脚连接，可以通过编程将 LE 与其他 LE 或 IOE 连接。

![FGPA 结构](/img/in-post/post-buaa-co/fpga-layout.png "fpga-layout"){:height="500px" width="500px"}

## 阵列实现

为了减少尺寸和成本，一般用 nMOS 或者动态电路实现 ROM 和 PLA 而非逻辑门。

在类 nMOS 实现中，译码器的输出被连接到 nMOS 的门上，只有下拉 nMOS 网络到 GND 没有路径时，弱上拉 pMOS 才输出高电平。

下拉 nMOS 被放在“点表示法”中每个没有点的交汇处。当译码器输出 1 时，对应的下拉 nMOS 被打开，输出 0，而字线上没有 nMOS 的地方由弱 pMOS 拉高至 1。

![类 nMOS 阵列 ROM](/img/in-post/post-buaa-co/rom-pseudo-nmos.png "rom-pseudo-nmos"){:height="600px" width="600px"}

逻辑阵列采用的原理类似。

![3\*3\*2 类 nMOS 阵列 PLA](/img/in-post/post-buaa-co/3-3-2-bit-pla-pseudo-nmos.png "3-3-2-bit-pla-pseudo-nmos"){:height="700px" width="700px"}

# 磁盘

磁盘通过磁头与介质的相对运动完成读写操作。
- 写入时根据写入代码确定写入驱动电流的方 向，使磁表面被磁化的极性方向不同，以区别“0”和“1”
- 读出时磁头相对磁化单元做切割磁力线运动，磁化单元的极性决定了感应电势的方向，以此区别“0”和“1”

## 磁记录编码方式

常用磁记录编码方式有归零制，不归零制，调相制，调频制。

![magnetic-recording-methods](/img/in-post/post-buaa-co/magnetic-recording-methods.png)

## 硬盘结构

一个磁盘包含若干盘片，每盘片分上下两个盘面，每个盘面由一个磁头负责读写。每个盘面可以分为若干同心圆环，即磁道。每个磁道包含若干扇区（默认 512B）。

## 磁盘性能

存储容量 $s$ = 磁头数（磁盘面数）$N_s$ * 磁道（柱面）数 $N_{cps}$ * 每道扇区数 $N_{tpc}$ * 每扇区字节数 $bpt$

访问时间 $T_A$ = 寻道时间 $T_S$ + 寻区时间 $T_w$

数据传输率 $D_r$ 表示单位时间内传输的数据位数。

## RAID

RAID（Reduntant Array of Independent Disks）由多个物理硬盘组成，被当作一个独立的硬盘。数据被分布在多个硬盘上，同时保存校验数据，可以用来恢复信息，并提升访问速度。

- RAID 0：不保存冗余信息，数据分布在多个物理磁盘上，可以实现 I/O 的并行，提高传输效率
- RAID 1：镜像硬盘。两组硬盘保存的数据完全一样。读操作由速度快的一组决定，写操作由速度慢的一组决定。成本比较高，数据恢复简单。
- RAID 2：数据条带较小，分布在不同磁盘上，多个磁盘使用并行同步访问。数据用海明码进行校验，校验码分布在冗余磁盘上。传输效率和访问效率高。
- RAID 3：类似于 RAID 2，使用奇偶校验码校验
- RAID 4：数据条带较大，使用奇偶校验码。写入数据需要重新计算校验码，写入较慢。
- RAID 5：类似于 RAID 4，奇偶校验吗保存在不同磁盘上

除此之外还有更高级的 RAID。

## 软盘

软盘也是一种磁盘，有 3.5inch 和 5.25inch 两种。

## 固态硬盘

固态硬盘（Solid-State Disk，SSD）是一种利用 Flash 存储器技术制造的硬盘。固态盘的内部氛围三部分：控制器芯片，嵌入式 CPU 的程序 RAM 和 Flash 芯片阵列。其中，控制器芯片用于在 Flash 芯片阵列上实现均衡存储数据以及交换数据。

# 光盘

## CD-ROM

CD-ROM 是一个直径 120mm，厚度 1.2mm，中心孔径 15mm 的同心圆盘。圆盘的表面有凸起。其中凹陷的部位称作 Pit，表示 0；凸起的部位表示 Land，表示 1。

总容量为 650MB。

## CD-R

用一层染料层记录数据，初始时所有点都是透明的。写入数据时，对应位置变为不透明点，表示 1。根据透明与否可以判断数据。注意不透明点不可以恢复成透明。

## CD-RW

和 CD-R 类似，用合金层代替染料层。合金为晶体时呈现透明，合金为无序状态时为不透明。

使用大功率激光照射，合金熔化，变为不透明。使用中等功率照射，合金熔化，变为透明。使用小功率照射时可以读取状态。

## DVD

DVD 和 CD-ROM 类似，但是 Pit 直径更小，数据密度更高，数据量和传输速率也更大。容量可达 4.7GB～17GB。