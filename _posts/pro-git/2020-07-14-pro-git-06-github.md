---
layout: "post"
title: "「Pro Git」 06 GitHub"
subtitle: "GitHub 的使用"
author: "roife"
date: 2020-07-14

tags: ["Pro Git@读书笔记", "读书笔记@Tags", "Git@Linux", "Linux@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# GitHub

## 贡献代码流程

1. Fork 项目
2. 创建新的 branch（可选）
3. 修改并 Commit
4. Push 到 GitHub
5. 发起 Pull Request
6. owner 进行 merge 或者 close PR

pull request 的使用技巧：

1. 可以边写代码边 pr，和项目负责人充分沟通
2. pr 中途要修改代码只要直接 push 就好，pr 记录会直接更新
3. 如果上游代码发生变动，可能会导致 pr 无法合并，此时一般手动将上游代码合并到 pr 中

``` shell
$ git remote add upstream <link>
$ git fetch upstream
$ git merge upstream/master
```

## 维护项目

### 快速合并 patch

``` shell
$ curl https://github.com/tonychacon/fade/pull/1.patch | git am
```

### 合并 pr 引用

用 `git ls-remote` 可以查看远程分支，其中以 `refs/pull/<pr#>/` 开头的分支表示指向 pr, `head`
结尾表示 pr 的最后一次提交，`merge` 表示对应的合并提交（普通分支用 `refs/heads/<branch>`).

``` shell
$ git ls-remote https://github.com/schacon/blink
10d539600d86723087810ec636870a504f4fee4d    HEAD
10d539600d86723087810ec636870a504f4fee4d    refs/heads/master
6a83107c62950be9453aac297bb0193fd743cd6e    refs/pull/1/head
afe83c2d1a70674c9505cc1d8b7d380d5e076ed3    refs/pull/1/merge
3c8d735ee16296c242be7a9742ebfbc2665adec1    refs/pull/2/head
15c9f4f80973a2758462ab2066b6ad9fe8dcf03d    refs/pull/2/merge
a5a7751a33b7e86c5e9bb07b26001bb17d775d1a    refs/pull/4/head
31a45fc257e8433c8d8804e3e848cf61c9d3166c    refs/pull/4/merge
```

如果要一次性抓取所有的 pr，需要在 `.git/config` 中添加

``` gitconfig
[remote "origin"]
  url = https://github.com/libgit2/libgit2.git
  fetch = +refs/heads/*:refs/remotes/origin/*
  fetch = +refs/pull/*/head:refs/remotes/origin/pr/* # 添加这一行
```

此时 fetch 就会抓取所有 pr。

``` shell
$ git checkout pr/2
Checking out files: 100% (3769/3769)，done.
Branch pr/2 set up to track remote branch pr/2 from origin.
Switched to a new branch 'pr/2'
```

### 在 pr 上开 pr

不仅可以选择在哪个 branch 上开 pr，还可以选择在 pr 上开 pr。
