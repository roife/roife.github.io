---
layout: "post"
title: "「Pro Git」 03 Git Branching"
subtitle: "Git 分支"
author: "roife"
date: 2020-07-13

tags: ["Pro Git@读书笔记", "读书笔记@Tags", "Git@Linux", "Linux@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Branch

每次 commit 时 git 会保存一个 commit object，包含一个指向 snapshot 的指针，父对象的指针和其它信息。

- 暂存操作：为每一个文件计算 checksum，然后把当前版本的文件快照保存到 Git 仓库中，最终将校验和加入到暂存区
- 提交操作：计算每一个子目录的校验和，然后所有 checksum 组织成一棵树，再创建一个 commit object

Git 的默认分支名字是 master，master 分支会在每次提交时自动向前移动。

一般开发会维护 master、develop、topic、proposed 等多个分支，其项目文件稳定性不同。topic 分支一般用于实现某个特定功能和修复特定 bug。

## 查看分支

- `git branch`：列出分支（用 `*` 标注分支代表当前分支，即 HEAD)
  - `-v`：查看每个分支最后一次提交
  - `merged {branch}` 与 `--no-unmerged {branch}`：查看已经合并或未合并到当前分支（在后面补充 branch 会显示相对于该分支的情况）

- `git log --decorate`：查看各个分支指向的对象

## 创建分支

- `git branch <branch>`：创建新分支

- `git checkout -b <branch>`：创建新分支同时切换过去
  - `git checkout -b <new_branch> <old_branch>`：在老分支的基础上建立新分支

git 中用 `HEAD` 指针指向当前分支。

``` shell
$ git branch testing
$ git log --oneline --decorate
f30ab (HEAD -> master, testing) add feature #32 - ability to add new formats to the central interface
34ac2 Fixed bug #1328 - stack overflow under certain conditions
98ca9 The initial commit of my project
```

![HEAD 指向 master 分支](/img/in-post/post-pro-git/head-to-master.png "head-to-master")

## 切换分支

- `git checkout <branch>`：切换分支

分支切换前最好提交或 stash 当前暂存区。

``` shell
$ git checkout testing
$ vim test.rb
$ git commit -a -m 'made a change'
```

![HEAD 随着提交向前移动](/img/in-post/post-pro-git/advance-testing.png
"advance-testing")

``` shell
$ git checkout master
$ vim test.rb
$ git commit -a -m 'made other changes'
```

![项目历史形成分支](/img/in-post/post-pro-git/advance-master.png "advance-master")

## 删除分支

- `git branch -d <branch>`：删除分支，对于未合并的分支会警告
- `git branch -D <branch>`：强行删除分支（相当于加了 `--force`）

## 合并分支

- `git merge <branch>`：合并分支与当前分支

合并两个分支时，如果一个分支是另一个的后继，指针就会直接右移，此时不需要解决什么冲突，即 fast-forward。（用 `--no-ff` 禁用）

当两个分支处于不同的树节点时，git 会利用两个节点以及其公共祖先进行合并，此时如果两个分支修改了同一个文件的同一处，就会发生冲突（可以用 `git status` 查看）。

``` shell
$ git merge iss53
Auto-merging index.html
CONFLICT (content): Merge conflict in index.html
Automatic merge failed; fix conflicts and then commit the result.

$ git status
On branch master
You have unmerged paths.
  (fix conflicts and run "git commit")

Unmerged paths:
  (use "git add <file>..." to mark resolution)

both modified:      index.html

    no changes added to commit (use "git add" and/or "git commit -a")
```

![一次合并的三个 snapshot](/img/in-post/post-pro-git/basic-merging-1.png "basic-merge-1")

![合并结果](/img/in-post/post-pro-git/basic-merging-2.png "basic-merge-2")

此时冲突文件中 `<`、`=`、`>` 三个标记组成的区域表示冲突部分，需要自行修改后 `add`、`commit`。或用 `git mergetool` 启动图形化工具。

``` html
<<<<<<< HEAD:index.html
<div id="footer">contact : email.support@github.com</div>
=======
<div id="footer">
 please contact us at support@github.com
</div>
>>>>>>> iss53:index.html
```

## 管理远程分支

- `git ls-remote <remote>`：获取远程引用的完整列表
- `git branch -a`：查看远程分支

远程分支是服务器上同步的分支版本，会用 `<remote>/<branch>` 的形式命名。（如 `origin/master` 修改后指向位置不变，而会多出新指针 `master`）

可以用 `git fetch <remote>` 拉取远程仓库。

![更新远程仓库](/img/in-post/post-pro-git/remote-branches.png "remote-branches")

注意远程仓库并不是一个真正的分支，而只是一个指针，需要用 `git checkout` 在其创建新分支才能使用。

### 跟踪远程分支

- `git checkout -b <branch> <remote>/<branch>`：创建一个跟踪分支

- `git checkout --track <remote>/<branch>`：创建新分支跟踪远程分支

- `git branch -u <remote/branch>` 或 `git branch --set-upstream-to <remote/branch>`：设置本地分支追踪远程分支

- `git branch -vv`：查看所有跟踪分支（最好先用 `git fetch -all` 拉取数据）

根据远程分支创建的本地分支会成为“跟踪分支”，其对应的远程分支称为“上游分支”（如 clone）

当试图 checkout 的分支并不存在，并且存在一个同名的远程分支时，也会自动创建跟踪分支。

可以用 `@{upstream}` 或 `@{u}` 代表上游分支，如 `git merge @{u}`。

### 删除远程分支

- `git push <remote> -d <branch>`：删除远程分支

## `rebase`

- `git rebase <target-branch>`：将当前分支 rebase 到目标分支

普通的 `merge` 是合并两个分支，而 `rebase` 是将某一个分支的变化提取出来，应用到另一个分支。（让提交历史更简洁）

### 简单的例子

``` shell
$ git checkout experiment
$ git rebase maste
First, rewinding head to replay your work on top of it...
Applying: added staged command
```

![原始状态](/img/in-post/post-pro-git/basic-rebase-1.png "basic-rebase-1")

![进行 rebase](/img/in-post/post-pro-git/basic-rebase-3.png "basic-rebase-3")

![合并 rebase 的结果](/img/in-post/post-pro-git/basic-rebase-4.png "basic-rebase-4")

``` shell
$ git checkout master
$ git merge experiment
```

### 对分支的分支上 rebase

- `git rebase --onto <master> <b1> <b2>` b2 是 b1 的分支，将 b2 这一条分支提取出来：rebase 到 master 上

![原始状态](/img/in-post/post-pro-git/interesting-rebase-1.png "interesting-rebase-1")

![进行 rebase](/img/in-post/post-pro-git/interesting-rebase-2.png "interesting-rebase-2")

### rebase 的风险

rebase 的本质是丢弃一些 commit 的记录，如果多个人对一个分支进行 rebase，会扰乱 commit 记录。

![原始状态](/img/in-post/post-pro-git/perils-of-rebasing-2.png "perils-of-rebasing-2")

![有人对远程仓库进行 rebase](/img/in-post/post-pro-git/perils-of-rebasing-3.png "perils-of-rebasing-3")

![再次 merge，远程仓库与本地仓库不同步](/img/in-post/post-pro-git/perils-of-rebasing-4.png "perils-of-rebasing-4")

所以使用 rebase 的时候要 branch 只有本地分支，或者其他人的机器上没有这个分支。

### 修复 rebase 带来的问题

一个方案是发生问题时不要 merge，用 rebase 处理 rebase，即 `git rebase teamone/master`。

![用 rebase 而不是 merge](/img/in-post/post-pro-git/perils-of-rebasing-5.png "perils-of-rebasing-5")

也可以手动进行 rebase，用 `git pull --rebase`（即 `git fetch` + `git rebase teamone/master`）代替 `git pull`。

- `git config --global pull.rebase true`：默认使用 `git pull rebase`

所以如果不得已需要对公有分支进行 rebase，最好通知所有人用 `git pull --rebase`。
