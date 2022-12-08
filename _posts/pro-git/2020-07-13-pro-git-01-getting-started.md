---
layout: "post"
title: "「Pro Git」 01 Getting Started"
subtitle: "认识 Git"
author: "roife"
date: 2020-07-13

tags: ["Pro Git@读书笔记", "读书笔记@Tags", "Git@Linux", "Linux@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Version Control

VCS（Version Control System）是用来管理文件的不同版本的系统。

- Local Version Control Systems（如 RCS）：在本地用数据库管理文件变更
- Centralized Version Control Systems（如 CVS、Subversion、Perforce）：文件版本信息存在服务器上，本地用客户端访问信息，易于管理但是依赖于服务器，存在文件丢失的隐患
- Distributed Version Control Systems（如 Git、Mercurial、Bazaar、Darcs）：将服务端的文件版本信息全部保存在本地，可以解决版本信息丢失的问题

# Git

## 文件快照（snapshots）

大部分 VCS 存储的是文件的变化，而 git 存储的是文件的快照，每个文件用 blob 对象保存。

## Checksum

Git 用 SHA-1 来计算校验和，并且用它来指向特定的文件。

## 三种状态

- Modified：已经修改但是没有 commit 的文件
- Staged：被标记的 Modified，将要 commit
- Committed：修改信息存入数据库

# 初始配置

- `git config`：配置 git

Git 将配置存放在三个地方

- `etc/gitconfig`：对于系统中每一个用户都生效，使用参数 `--system`（需要管理员权限）
- `~/.gitconfig` 或 `~/.config/git/config`：对当前用户生效，使用参数 `--global`
- `./.git/config`（默认）：对当前 repo 生效，使用参数 `--local`

其中仓库中的配置会覆盖用户配置，用户配置会覆盖系统配置。

- `git config <key>`：显示单项配置
- `git config --list {--show-origin}`：显示所有配置，相同的变量可能会出现多次（出现在不同的配置中），以靠后的为准
  - `--show-origin`：显示配置所在文件

## Identity

``` shell
$ git config --global user.name "roife"
$ git config --global user.email roifewu@gmail.com
```

## Editor

设置编辑器来输入信息，默认使用系统默认的编辑器。不同编辑器需要不同的配置（见附录）。

``` shell
$ git config --global core.editor emacs
```

# Help

以下三种查询 manpage 方式等价。

- `git help <verb>`
- `git <verb> --help`
- `man git-<verb>`

也可以用 `-h` 查询简要的帮助信息。
