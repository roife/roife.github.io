---
layout: "post"
title: "「BUAA-OS-Lab」 Lab0 Linux、Git 基础知识"
subtitle: "Shell 与 Git 的使用"
author: "roife"
date: 2021-03-30

tags: ["北航 OS 实验@课程相关", "课程相关@Tags", "操作系统@Tags", "Bash@编程语言", "Linux@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
katex: true
---

# 课上

## Exam

### Task 1

#### 题目

主要考察 `grep` 和 `find` 命令的用法。

首先新建 `dst_exam` 文件夹并在其中新建 `test.sh` 脚本，实现以下功能。

在当前目录找到所有包含 `hello OS lab0` **内容**的文件，将结果保留行号重定向**覆盖**到 `lab0_exam.c`。

然后找到所有**文件名**包含 `lab0_x` 的文件，将结果**追加**到 `lab0_exam.c`。

#### 分析

```bash
grep -rn 'hello OS lab0' . > lab0_exam.c
find . -name 'lab0_x' >> lab0_exam.c
```

### Task 2

#### 题目

主要考察 `Makefile` 的写法。

修改 `csc` 下面的 Makefile，使得执行 `make clean` 的时候保留 `csc/code/fibo.o`，删除 `csc/code/main.o` 和 `csc/fibo`。

#### 分析

```makefile
clean:
    rm code/main.o
    rm ./fibo
```

## Extra

### Task 1

#### 题目

首先进入 `ext_examA` 目录。

编写 Makefile，编译 `programA.c` 文件，生成可执行文件 `programA`。

编写脚本 `script.sh`，传入文件名参数，查找传入文件名对应文件的第 8 行的内容，将查找结果作为输入传递到 `./programA` 中，并且将输出结果重定向**覆盖**到 `outputA`。

#### 分析

```makefile
all: programA.c
        gcc programA.c -o programA
clean: programA.c
        rm programA
```

```shell
sed -n '8p' $1 | ./programA > outputA
```

### Task 2

#### 题目

进入 `ext_examB`，编写脚本 `findX.sh`。

在 `test_dir` 目录下找到 `xfile` 文件，然后将其内容中所有的的 `char` 改为 `int`，并且将结果输出到 `output`文件

#### 分析

```shell
find test_dir/ -name 'xfile' | xargs sed 's/char/int/g' > output
```
