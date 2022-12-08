---
layout: "post"
title: "「Pro Git」 07 Git Tools (unfinished)"
subtitle: "Git 高级命令"
author: "roife"
date: 2020-07-21

tags: ["Pro Git@读书笔记", "读书笔记@Tags", "Git@Linux", "Linux@Tags", "未完成@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 选择修订的版本

## SHA-1

SHA-1 长度为 20 字节，一般提供前几个字节，git 就能找到对应的 commit。

``` shell
$ git show 1c002dd4b536e7479fe34593e72e6c6c1819e53b
$ git show 1c002dd4b536e7479f
$ git show 1c002d
```

## 分支名称

可以用分支名称指代该分支最顶端的 commit。

``` shell
$ git show ca82a6dff817ec66f44342007202690a93763949
$ git show topic1
# 用 rev-parse 找分支名相应的 SHA-1
$ git rev-parse topic1
ca82a6dff817ec66f44342007202690a93763949
```

## reflog

git 的 reflog 记录了最近一段时间 HEAD 和各个 branch 指向的历史。

- `git reflog`：查看 reflog
- `git log -g <branch>`：查看详细的 reflog 信息

``` shell
$ git reflog
734713b HEAD@{0}: commit: fixed refs handling, added gc auto, updated d921970 HEAD@{1}: merge phedders/rdocs: Merge made by the 'recursive' strategy.
1c002dd HEAD@{2}: commit: added some blame and merge stuff
1c36188 HEAD@{3}: rebase -i (squash): updating HEAD
95df984 HEAD@{4}: commit: # This is a combination of two commits. 1c36188 HEAD@{5}: rebase -i (squash): updating HEAD
7e05da5 HEAD@{6}: rebase -i (pick): updating HEAD
```

可以用 `git show` 查看对应的引用日志和提交：

``` shell
$ git show HEAD@{5}
$ git show master@{yesterday}
$ git show master@{2.months.ago}
```

## 祖先引用

在引用的尾部用 `^` 来引用当前提交的上一个提交，多个 `^` 连用或者 `^{n}` 表示第几个父提交（并列提交之间选择）。

``` shell
$ git show HEAD^ # HEAD 的上一个父提交
$ git show HEAD^^ # HEAD 的上一个父提交中并列的第二个
```

在引用的尾部用 `~` 表示上一个父提交，多个 `~` 连用或者 `~{n}` 表示几个之前的父提交（前后选择）。

`^` 和 `~` 的区别在于，一个是横向选择，一个是纵向选择。如 `HEAD~3^2` 表示当前引用的第三个历史提交中第二个并列提交。

## 提交区间

### 双点

用 `..` 可以查看在一个分支中而不在另一个分支中的提交。

![区间提交的例子](/img/in-post/post-pro-git/double-dot.png "double-dot")

``` shell
$ git log master..experiment
D
C
$ git log experiment..master
F
E
```

### 多点

用 `^` 或者 `--not` 可以用来表示不希望被包含的提交。

``` shell
# 以下三个命令等价
$ git log refA..refB
$ git log ^refA refB
$ git log refB --not refA

# 查看同时被 refA 和 refB 包含，但是不被 refC 包含的提
$ git log refA refB ^refC
$ git log refA refB --not refC
```

### 三点

用 `...` 可以查看两个引用的祖先中不公有的提交。

``` shell
$ git log master...experiment
F
E
D
C
```

加上 `--left-right` 参数可以指明哪个提交是左边的，哪个是右边的。

``` shell
$ git log --left-right master...experiment
< F
< E
> D
> C
```

# 交互式暂存

`git add` 时用 `-i` 或 `--interactive` 可以用交互式进行暂存。

``` shell
$ git add -i
           staged     unstaged path
  1:    unchanged        +0/-1 TODO
  2:    unchanged        +1/-1 index.html
  3:    unchanged        +5/-1 lib/simplegit.rb

***Commands***  ,***Commands***
  1: status     2: update      3: revert     4: add untracked
  5: patch      6: diff        7: quit       8: help
What now>
```

## 交互式暂存补丁

用 `git add -p` 或者 `git add --patch` 可以暂存文件部分区块的变化。

同理，可以用 `git reset -p`、`git checkout -p` 和 `git stash save -p` 对文件的部分区域操作。

# `stash`

`stash` 会跟踪工作区和暂存区，将未完成的工作保存起来，此时恢复到上一个 commit 的情况，这样不需要进行 commit 也能随意切换 branch 了。

- `git stash` 或 `git stash push`：将修改保存到栈里
  - `--keep-alive`：只 stash 没有暂存的文件
  - `-u` 或 `--include-untracked`：stash 未跟踪的文件（默认只 stash 跟踪的文件）
  - `-a` 或 `--all`：stash 所有文件，包括未跟踪的和 ignore 的（默认不会 stash ignore 的文件）
  - `-p` 或 `--patch`：交互式地 stash 部分文件区块

- `git stash list`：查看栈里的 stash

- `git stash apply`：恢复最近的 stash，如果恢复时有冲突需要合并冲突，默认暂存的文件不会重新暂存
  - `git stash apply stash@{number}`：恢复特定的 stash
  - `--index`：之前暂存区的文件仍放到暂存区中

- `git stash drop stash@{number}`：移除指定的 stash

- `git stash clear`：清除所有 stash

- `git stash branch <branch>`：在 stash 的工作上创建新的分支，自动 checkout 并 drop

# 清理工作区文件

- `git clean`：删除所有未追踪的文件
  - `-f`：强制删除
  - `-n` 或 `--dry-run`：告知会删除什么
  - `-x`：同时删除 ignore 的文件
  - `-i`：交互式地删除
  - `-d`：删除目录

使用前可以用 `git stash --all` 来 stash 文件，防止错删。

项目存在 submodule 时可能需要 `git clean -fd -f`。

# 签署代码

首先保证已经用 GPG 生成了密钥，可以用 `gpg --gen-key` 生成并用 `gpg --list-keys` 查看。

- `git config --global user.singningkey <key>`：设置签署密钥

## 签署 tag

- `git tag -s <tag-name> -m <message>`：用 `-s` 代替 `-a` 来签署标签

此时使用 `git show` 就能看到签署的密钥。

``` shell
$ git tag -s v1.5 -m 'my signed 1.5 tag'

You need a passphrase to unlock the secret key for
user: "Ben Straub <ben@straub.cc>"
2048-bit RSA key, ID 800430EB, created 2014-05-04
```

## 验证 tag

- `git tag -v <tag-name>`：验证 tag 签名

验证 tag 需要先把签署者的公钥保存在 keyring 中，否则会报错。

``` shell
$ git tag -v v1.4.2.1
object 883653babd8ee7ea23e6a5c392bb739348b1eb61
type commit
tag v1.4.2.1
tagger Junio C Hamano <junkio@cox.net> 1158138501 -0700

GIT 1.4.2.1

Minor fixes since 1.4.2, including git-mv and git-http with alternates.
gpg: Signature made Wed Sep 13 02:08:25 2006 PDT using DSA key ID F3119B9A
gpg: Good signature from "Junio C Hamano <junkio@cox.net>"
gpg:                 aka "[jpeg image of size 1513]"
Primary key fingerprint: 3565 2A26 2040 E066 C9A7  4A7D C0C6 D9A4 F311 9B9A
```

## 签署 commit

同理 commit 的时候加上 `-S` 就能签署 commit。

``` shell
$ git commit -a -S -m 'Signed commit'

You need a passphrase to unlock the secret key for
user: "Scott Chacon (Git signing key) <schacon@gmail.com>"
2048-bit RSA key, ID 0A46826A, created 2014-06-04

[master 5c3386c] Signed commit
4 files changed, 4 insertions(+), 24 deletions(-)
rewrite Rakefile (100%)
create mode 100644 lib/git.rb
```

- `git log --show-signature`：查看签名

`git merge` 也能用 `-S` 来签署合并提交。

`git merge` 和 `git pull` 也能用 `--verify-signatures` 来检查签名，并且会拒绝没有有效签名的提交。

# 搜索

## git grep

- `git grep`：查找工作区文件

  - `-n` 或 `--line-number`：显示行号
  - `-c` 或 `--count`：输出每个文件有多少匹配
  - `-p` 或 `--show-function`：显示匹配所在的函数
  - `--and`：多个出现在同一行的匹配

``` shell
$ git grep --break --heading \
  -n -e '#define' --and \( -e LINK -e BUF_MAX \) v1.8.0
v1.8.0:builtin/index-pack.c
62:#define FLAG_LINK (1u<<20)

v1.8.0:cache.h
73:#define S_IFGITLINK  0160000
74:#define S_ISGITLINK(m)       (((m) & S_IFMT) == S_IFGITLINK)

v1.8.0:environment.c
54:#define OBJECT_CREATION_MODE OBJECT_CREATION_USES_HARDLINKS

v1.8.0:strbuf.c
326:#define STRBUF_MAXLINK (2*PATH_MAX)

v1.8.0:symlinks.c
53:#define FL_SYMLINK  (1 << 2)

v1.8.0:zlib.c
30:/* #define ZLIB_BUF_MAX ((uInt)-1) */
31:#define ZLIB_BUF_MAX ((uInt) 1024 * 1024 * 1024) /* 1GB */
```

## 日志搜索

用 `-S` 参数可以显示某一字符串被新增或删除时的提交。

用 `-G` 可以用正则表达式进行搜索。

``` shell
$ git log -S ZLIB_BUF_MAX --oneline
e01503b zlib: allow feeding more than 4GB in one go
ef49a7a zlib: zlib can only process 4GB at a time
```

## 行日志搜索

- `git log <start>,<end>:<file>` 或 `git log -L :<funcname>:<file>` 或：`git log -L <regex>:<file>`：查看某一行或某个函数或匹配正则表达式的变化历史

``` shell
$ git log -L :git_deflate_bound:zlib.c
commit ef49a7a0126d64359c974b4b3b71d7ad42ee3bca
Author: Junio C Hamano <gitster@pobox.com>
Date:   Fri Jun 10 11:52:15 2011 -0700

zlib: zlib can only process 4GB at a time

diff --git a/zlib.c b/zlib.c
--- a/zlib.c
+++ b/zlib.c
@@ -85,5 +130,5 @@
-unsigned long git_deflate_bound(z_streamp strm, unsigned long size)
+unsigned long git_deflate_bound(git_zstream *strm, unsigned long size)
{
    -       return deflateBound(strm, size);
    +       return deflateBound(&strm->z, size);
}
```

# 重写历史

在推送之前可以随意更改提交的内容，但是要保证推送之后不再对提交进行修改，否则可能就会遇到冲突。

## 修改最后一次提交

- `git commit --amend`：将当前暂存区合并到上一次提交（会改变 SHA-1）
  - `--no-edit`：不编辑提交 commit message

## 修改多个提交信息

## 排序 commit

## 拆分 commit

## `filter-branch`

# `reset`

**\***
