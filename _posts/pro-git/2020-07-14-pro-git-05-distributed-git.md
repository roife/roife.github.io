---
layout: "post"
title: "「Pro Git」 05 Distributed Git"
subtitle: "分布式 Git 使用的工作流程"
author: "roife"
date: 2020-07-14

tags: ["Pro Git@读书笔记", "读书笔记@Tags", "Git@Linux", "Linux@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 工作流

## Centrailized Workflow

最普通的中心式工作流

![Centrailized Workflow](/img/in-post/post-pro-git/centralized_workflow.png "centralized workflow")

## Integration-Manager Workflow

1. contributor 克隆 repo 并修改，然后将代码推送到自己的 public repo
2. contributor 给维护者发消息请求合并
3. 维护者将 contributor 的仓库添加为 remote 并合并修改
4. 维护者将修改推送到主仓库

这是 GitHub 采用的模式

![Integration-Manager Workflow](/img/in-post/post-pro-git/integration-manager.png "integration-manager workflow")

## Dictator and Lieutenants Workflow

1. 普通开发者在自己的 branch 上进行 rebase
2. lieutenants 将普通开发者的 branch 合并到自己的 master 分支
3. dictator 将 lieutenants 的 master 分支合并到自己的 master 分支
4. dictator 将 master 分支推送到仓库

这是非常大的项目（如 Linux）采用的模式。

![Dictator and Lieutenants Workflow](/img/in-post/post-pro-git/benevolent-dictator.png "dictator and lieutenants workflow")

# Commit Guidelines

- 一个 commit 只解决一个问题
- commit message 要遵从一定的格式
- 提交之前用 `git diff --check` 检查有没有小错误

# 贡献代码

## 私有小团队工作流

一般是两三个人对一个私有的 repo 进行贡献。

push 之前 fetch，如果有未合并的分支则先 merge 再 push。

![私有小团队工作流](/img/in-post/post-pro-git/small-team-flow.png "small-team-flow")

## 私有管理团队

采用 integration-manager workflow。

开发者在多个不同的 feature branch 上工作，只有管理员能将 feature branch 的内容推送到 master 分支。

![私有管理团队工作流](/img/in-post/post-pro-git/managed-team-flow.png "managed-team-flow")

## 公有项目

fork 项目后工作，然后发起 pr 请求合并。

一般先 clone 原项目，然后 fork 并在本地添加 remote 仓库。

- `git request-pull <remote1/branch> <remote2>`：产生一个 remote2 向 remote1/branch 的 pr（需要先把本地 commit 推送到自己的远程仓库）

``` shell
$ git checkout -b featureB origin/master
... work ...
$ git commit
$ git push myfork featureB
$ git request-pull origin/master myfork
... email generated request pull to maintainer ...
$ git fetch origin
```

一般 master 分支用来追踪 origin/master，写新的 feature 时直接从 master 分支开始而不是其它分支，这样不会产生依赖。

产生冲突时可以尝试用 rebase 来帮助维护者解决冲突。

![原始状态](/img/in-post/post-pro-git/public-small-1.png "public-small-1")

``` shell
# 比如尝试把 featureA rebase 到 master 并更新 pr
$ git checkout featureA
$ git rebase origin/master
$ git push -f myfork featureA
```

![本地 rebase 后推送](/img/in-post/post-pro-git/public-small-2.png "public-small-2")

- `git merge --squash <branchA>`：将分支 A 的多个 commit 合并成一个放到当前分支

``` shell
$ git checkout -b featureBv2 origin/master
$ git merge --squash featureB
... change implementation ...
$ git commit
$ git push myfork featureBv2
```

![使用 –squash 选项合并提交](/img/in-post/post-pro-git/public-small-3.png "public-small-3")

## 基于邮件的公开项目

一些历史悠久的大型项目只通过开发者邮件列表接受补丁。

- `git format-patch <commit>` 或 `git format-patch <branch>`：将每一个 commit 转换为邮件，邮件标题为 commit message 的第一行
  - `-M`：检测 commit 是否重命名

``` shell
$ git format-patch -M origin/master
0001-add-limit-to-log-function.patch
0002-changed-log-output-to-30-from-25.patch
```

可以用 `$ cat` 来输出补丁的信息，也可以直接编辑这些补丁文件。

``` shell
$ cat 0001-add-limit-to-log-function.patch
From 330090432754092d704da8e76ca5c05c198e71a8 Mon Sep 17 00:00:00 2001
From: Jessica Smith <jessica@example.com>
Date: Sun, 6 Apr 2008 10:17:23 -0700
Subject: [PATCH 1/2] add limit to log function

Limit log functionality to the first 20

---
# 这里可以随意添加注释消息
lib/simplegit.rb |    2 +-
1 files changed, 1 insertions(+), 1 deletions(-)

diff --git a/lib/simplegit.rb b/lib/simplegit.rb
index 76f47bc..f9815f1 100644
--- a/lib/simplegit.rb
+++ b/lib/simplegit.rb
@@ -14,7 +14,7 @@ class SimpleGit
end

def log(treeish = 'master')
-    command("git log #{treeish}")
+    command("git log -n 20 #{treeish}")
end

def ls_tree(treeish = 'master')
--
2.1.0
```

可以用 git 直接通过 IMAP 或者 SMTP 发送补丁文件。

### 通过 IMAP 发送邮件到草稿箱

首先在 `.gitconfig` 中配置

``` gitconfig
[imap]
  folder = "[Gmail]/Drafts"
  host = imaps://imap.gmail.com
  user = user@gmail.com # 邮件地址
  pass = YX]8g76G_2^sFbd # 邮件密码
  port = 993
  sslverify = false
```

然后用 `git imap-send`。

``` shell
$ cat *.patch |git imap-send
Resolving imap.gmail.com... ok
Connecting to [74.125.142.109]:993... ok
Logging in...
sending 2 messages
100% (2/2) done
```

最后到草稿箱里面编辑信息并发送文件。

### 通过 SMTP 发送邮件

在 `.gitconfig` 中配置

``` gitconfig
[sendemail]
  smtpencryption = tls
  smtpserver = smtp.gmail.com
  smtpuser = user@gmail.com
  smtpserverport = 587
```

然后用 `git send-email` 发送邮件。

``` shell
$ git send-email *.patch
0001-added-limit-to-log-function.patch
0002-changed-log-output-to-30-from-25.patch
Who should the emails appear to be from? [Jessica Smith <jessica@example.com>]
Emails will be sent from: Jessica Smith <jessica@example.com>
Who should the emails be sent to? jessica@example.com
Message-ID to be used as In-Reply-To for the first email? y
```

# 维护项目

## Topic Branches

作为维护者，可以先将收到的 pr 放到某个 topic branch，命名为 `<sender/topic>`。

## 应用邮件补丁

### 应用 `diff` 的补丁：`apply`

- `git apply <patch_dir>`：应用某个补丁
- `git apply --check <patch_dir>`：检查某个补丁

`git apply` 采用的是 `apply all or abort all` 的模型，如果补丁有异常则整个补丁都不会被应用。

``` shell
$ git apply --check 0001-seeing-if-this-helps-the-gem.patch
error: patch failed: ticgit.gemspec:1
error: ticgit.gemspec: patch does not apply
```

### 应用 `format-patch` 的补丁：`am`

`git format-patch` 形成的文件类似于 mbox 文件，需要先下载然后使用。

- `git am <patch_dir>`：应用补丁

  - `-i`：进入交互模式，一个 mbox 有多个补丁时使用

此时会自动创建一个 commit，作者信息是电子邮件的 From 和 Date，提交消息是 Subject 和邮件正文中补丁之前的内容。

如果有冲突就会停下来询问该怎么做。

``` shell
$ git am 0001-seeing-if-this-helps-the-gem.patch
Applying: seeing if this helps the gem
error: patch failed: ticgit.gemspec:1
error: ticgit.gemspec: patch does not apply
Patch failed at 0001.
When you have resolved this problem run "git am --resolved".
If you would prefer to skip this patch, instead run "git am --skip".
To restore the original branch and stop patching run "git am --abort".
```

如果补丁是在当前仓库内部某个 commit 的（否则将无效），可以用 `-3` 让 git 使用三方合并。

``` shell
$ git am -3 0001-seeing-if-this-helps-the-gem.patch
Applying: seeing if this helps the gem
error: patch failed: ticgit.gemspec:1
error: ticgit.gemspec: patch does not apply
Using index info to reconstruct a base tree...
Falling back to patching base and 3-way merge...
No changes -- Patch already applied.
```

## `checkout` 远程分支

贡献者 fork 了远程仓库，然后发邮件请求合并，本地添加远程仓库并且进行合并。

这种方法的优势在于 git 会默认进行三方合并。

``` shell
$ git remote add jessica git://github.com/jessica/myproject.git
$ git fetch jessica
$ git checkout -b rubyclient jessica/ruby-client
# 或者不添加 remote 直接 pull
$ git pull https://github.com/onetimeguy/project
From https://github.com/onetimeguy/project
* branch            HEAD   -> FETCH_HEAD
Merge made by the 'recursive' strategy.
```

## 查看引入的 commit

### 对比一个分支与另一分支

- `git diff <branchA> <branchB>` 或 `git diff <branchA>..<branchB>`：对比 A 与 B 上的最新提交

### 对比分支到祖先的提交

一种方法是用 `git merge-base` 先找到祖先然后进行 `diff`；也可以直接用 `git diff` 的三点语法。

- `git diff <branchA>...<branchB>`：查看 B 到 A 和 B 的公共祖先的修改

``` shell
$ git diff $(git merge-base contrib master)
# 等价形式
$ git diff master...contrib
```

## 整合贡献

- 最简单的是只维护一个 master 分支，每次直接将代码整合到 master 中
- 对于稍微大一点的项目，一般会维护 master 和 develop 两个分支，其中 master 是非常稳定的版本。打 tag 后才将 develop 合并到 master
- 对于更大的项目，会维护更多分支。如 master 是稳定版本，next 是安全问题，pu 是功能更新，maint 是向后移植工作
- 一些维护者喜欢一直用 rebase 来形成线形的历史或者用 `git cherry-pick`

## `cherry-pick`

- `git cherry-pick <SHA-1>`：将某次 commit rebase 到当前分支（会得到一个新的 SHA-1），然后可以丢弃原分支

![原始状态](/img/in-post/post-pro-git/rebasing-1.png "rebasing-1")

![进行 cherry-pick](/img/in-post/post-pro-git/rebasing-2.png "rebasing-2")

## 打 tag

### 签名

一般打标签会进行签名。

git 内会用 blob 对象存储公钥。

``` shell
# 用 gpg 列出公钥
$ gpg --list-keys
/Users/schacon/.gnupg/pubring.gpg
---------------------------------
pub   1024D/F721C45A 2009-02-09 [expires: 2010-02-09]
uid                  Scott Chacon <schacon@gmail.com>
sub   2048g/45D02282 2009-02-09 [expires: 2010-02-09]

# 导出 key 并且传给 git hash 生成 blob，返回 SHA-1
$ gpg -a --export F721C45A | git hash-object -w --stdin
659ef797d181633c87ec71ac3f9ba29fe5775b92

# 创建标签
$ git tag -a maintainer-pgp-pub 659ef797d181633c87ec71ac3f9ba29fe5775b92

# 推送标签
$ git push --tags
```

校验者需要先导入 key 到 gpg，然后进行校验。

``` shell
# 导入 key
$ git show maintainer-pgp-pub | gpg --import
```

### 生成版本号

- `git describe`：让 git 自动生成一个版本号，包含 tag 及上次至今的提交数和 SHA-1
  - `--tags`：使用 lightweight tag

``` shell
$ git describe master
v1.6.2-rc1-20-g8c5b85c
```

### 准备发布

- `git archive`：创建压缩包

``` shell
# 创建 tar
$ git archive master --prefix='project/' | gzip > `git describe master`.tar.gz
# 创建 zip
$ git archive master --prefix='project/' --format=zip > `git describe master`.zip
```

### 发布简报

- `git shortlog`：快速生成发布简报和 changelog

``` shell
$ git shortlog --no-merges master --not v1.0.1
Chris Wanstrath (6):
      Add support for annotated tags to Grit::Tag
      Add packed-refs annotated tag support.
      Add Grit::Commit#to_patch
      Update version and History.txt
      Remove stray `puts`
      Make ls_tree ignore nils

Tom Preston-Werner (4):
      fix dates in history
      dynamic version method
      Version bump to 1.0.2
      Regenerated gemspec for version 1.0.2
```
