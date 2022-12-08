---
layout: "post"
title: "「Pro Git」 02 Git Basics"
subtitle: "基本命令"
author: "roife"
date: 2020-07-13

tags: ["Pro Git@读书笔记", "读书笔记@Tags", "Git@Linux", "Linux@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 创建 repo

- `git init`：在当前目录下建立一个 repo
  - `-o <remote>`：指定远程仓库名字

``` shell
# 通过以下命令进一步 track 文件
$ git add *.c
$ git add LICENSE
$ git commit -m 'Initial project version'
```

- `git clone <url> {dir}`：克隆一个 repo（`dir` 表示存放位置，默认存放在 repo 名字的文件夹中）

# 基本命令

repo 中的文件可以分为以下几种：

- Untracked
- Tracked
  - Unmodified
  - Modified
  - Staged

![文件的状态变化](/img/in-post/post-pro-git/lifecycle.png "lifecycle")

## add

- `git add <files>`：追踪一个文件

## status

- `git status`：查看仓库中文件的状态
  - `-s` 和 `--short`：用紧凑的方式查看 status

修改了一个处于 staged 状态的文件，该文件会同时出现在 staged 和 modified 的区域中。

使用 `-s` 时左边一栏表示 staged 区中的状态，右边一栏表示工作区的状态。

``` shell
$ git status -s
 M README             # 修改过，未暂存的文件（modified）
MM Rakefile           # 修改过，已暂存，并且再次修改
M  lib/simplegit.rb   # 修改过，已暂存的文件（staged）
A  lib/git.rb         # 新暂存的文件
?? LICENSE.txt        # 未追踪的文件（untracked）
```

## diff

- `git diff`：比较工作区和暂存区文件的差异
  - `--staged` 或 `--cached`：比较暂存区与上一次提交文件的差异

可以用 `git difftool` 调用外部 diff 工具来显示文件差异

## commit

- `git commit {-m "messages"}`：提交暂存区的修改，如果没有 `-m` 参数会自动启动编辑器来添加修改信息
  - `-a`：自动将追踪的文件暂存并提交，即自动 `add`

``` shell
$ git commit -m "Story 182: Fix benchmarks for speed"
[master 463dc4f] Story 182: Fix benchmarks for speed # 463dc4f 是校验和
 2 files changed, 2 insertions(+)
 create mode 100644 README
```

## 删除文件

- `git rm <files/patterns>`：删除文件，并且不再追踪它。对于已修改或已暂存的文件要加 `-f` 选项
  - `--cached`：不再追踪文件，但是并不删除

手动删除和用 `git rm` 的区别在于，手动删除要先 `add` 再 `commmit`，用 `git rm` 则可以直接 `commit`。

## 重命名文件

- `git mv <file1> <file2>`：将文件 1 改名为文件 2

``` shell
$ git mv README.md README
# 等价于执行了三条命令
$ mv README.md README
$ git rm README.md
$ git add README
```

# 忽略文件（gitignore）

可以在 `gitignore` 文件列出要忽略的文件，其规范如下：

- 所有空行或以 `#` 开头的行都会被忽略
- 可以使用标准的 glob 模式，并且会递归地进行匹配
  - `*` 匹配零个或多个任意字符
  - 方括号匹配一个其中的字符（如 `[abc]` 匹配一个 a 或 b 或 c）
  - `?` 匹配一个字符
  - 在方括号中用 `-` 可以表示范围（如 `\[0-9\]` 匹配 0 到 9）
  - `**` 匹配任意中间目录（如 `a/**/z` 匹配 `a/z`，`a/b/z` 或 `a/b/c/z`）
- 以 `/` 开头可以防止递归
- 以 `/` 结尾可以指定所在目录
- 以 `!` 开头表示取反，用来忽略一些模式

``` gitignore
# 忽略所有的 .a 文件
*.a

# 将 lib.a 排除忽略
!lib.a

# 只忽略当前目录下的 TODO 文件，而不忽略 subdir/TODO
/TODO

# 忽略任何目录下名为 build 的文件夹
build/

# 忽略 doc/notes.txt，但不忽略 doc/server/arch.txt
doc/*.txt

# 忽略 doc/ 目录及其所有子目录下的 .pdf 文件
doc/**/*.pdf
```

GitHub 上针对各门语言的 [.gitignore 文件](https://github.com/github/gitignore)

子文件夹也可以有独立的 `.gitignore` 文件。

# 历史（log）

- `git log`：查看提交历史，最近的提交在最上面
  - `-p` 或 `--patch`：显示每次提交的差异
  - `--stat`：显示 diff 的统计信息
  - `--shortstat`：只显示 `--stat` 中最后的行数修改添加移除统计
  - `--name-only`：仅显示修改文件的文件名
  - `--name-status`：显示新增、修改、删除的文件清单
  - `--abbrev-commit`：仅显示 SHA-1 校验和所有 40 个字符中的前几个字符
  - `--relative-date`：使用相对日期
  - `--graph`：用图形的方式显示分支信息
  - `--oneline`：即 `--pretty=oneline --abbrev-commit`
  - `--pretty=<options>`：用一些选项格式化输出，如 `oneline`、`short`、`full`、`fuller`、`format` 等，其中 `format` 可以自定义输出的格式
  - `-<num>`：来限制显示的 log 数目
  - `--since`、`--until`

``` shell
$ git log --pretty=format:"%h - %an, %ar : %s"
ca82a6d - Scott Chacon, 6 years ago : changed the version number
085bb3b - Scott Chacon, 6 years ago : removed unnecessary test
a11bef0 - Scott Chacon, 6 years ago : first commit
```

| 选项  | 含义                                         |
| ----- | -------------------------------------------- |
| `%H`  | 提交的完整哈希值                             |
| `%h`  | 提交的简写哈希值                             |
| `%T`  | 树的完整哈希值                               |
| `%t`  | 树的简写哈希值                               |
| `%P`  | 父提交的完整哈希值                           |
| `%p`  | 父提交的简写哈希值                           |
| `%an` | 作者名字                                     |
| `%ae` | 作者的电子邮件地址                           |
| `%ad` | 作者修订日期（可以用 –date=选项 来定制格式）|
| `%ar` | 作者修订日期，按多久以前的方式显示           |
| `%cn` | 提交者的名字                                 |
| `%ce` | 提交者的电子邮件地址                         |
| `%cd` | 提交日期                                     |
| `%cr` | 提交日期（距今多长时间）                    |
| `%s`  | 提交说明                                     |
| `%G?` | 是否签署                                     |
| `%GG` | GPG 原始验证信息                             |
| `%GS` | 签署者姓名                                   |

`format` 常用选项

# 撤消

## 修改上一次提交

- `git commit --amend`：将当前暂存区文件合并到上一次提交，并且重新编辑提交信息

## 恢复工作区的文件（撤销修改）

- `git checkout -- <file>`：将文件恢复到暂存时或者上一次提交的样子

## 取消一个文件的暂存

- `git reset HEAD <file>`：取消一个文件的暂存

## 丢弃提交

- `git reset --hard <SHA-1>`：回到某一个版本，丢弃之后的提交

可以用 `git reflog` 找回丢弃的提交，但是有时间限制。

# 远程仓库

- `git remote`：查看远程仓库服务器
  - `-v`：查看远程仓库 URL
  - `add <shortname> <url>`：添加一个远程仓库
  - `show <remote>`：查看某个远程仓库的信息
  - `rename <nameA> <nameB>`：修改远程仓库的缩写名
  - `remove <remote>` 或 `rm <remote>`：移除一个远程仓库

## Fetch

- `git fetch <remote>`：拉取一个仓库的数据，但是并不执行合并操作

## Pull

- `git pull`：追踪远程分支，拉取数据并尝试合并（fetch + merge）

## Push

- `git push <remote> <branch>`：将本地的分支推送到远程仓库，如果有他人推送了则应该先拉取再推送
  - `git push <remote> <local_branch>:<remote_branch>`：推送本地分支到远程分支
    - 如将本地的 `master` 推送到远程的 `qa/master`：`$ git push origin master:refs/heads/qa/master`

git clone 命令会自动设置本地 master 分支跟踪克隆的远程仓库的 master 分支，并将拉取的仓库名字设置为 origin。

# 打标记（tag）

可以为重要的 commit 打上标签。

- `git tag`：列出所有标签
  - `-l <pattern>` 或 `--list <pattern>`：列出匹配的标签
  - `-r`：查看远程标签

- `git show`：查看标签及对应的信息

``` shell
$ git tag -l "v1.8.5*"
v1.8.5
v1.8.5-rc0
```

标签分为两类。

- `lightweight`：不会改变分支，只是标记某个提交，一般是临时的
- `annotated`：是数据库中一个完整的对象，可以被校验并且包含其它信息

## 创建 tag

- `git tag <tagname>`：在当前提交打上 lightweight tag，不需要 messages 等信息
- `git tag -a <tagname>`：在当前提交创建 annotated tag
  - `-m <"messages">`：存储在标签的信息，若不加则会启动编辑器输入
- `git tag -a <tagname> <checksum>`：为对应 checksum 的版本打 tag

## 远程标签

### Push tag

打完标签要手动 push 标签

- `git push <remote> <tagname>`：推送标签
- `git push <remote> --tags`：推送所有标签

### Pull tag

- `git pull <remote> --tags`：拉取所有标签

## 删除 tag

- `git tag -d <tagname>`：删除标签
- `git push <remote> :refs/tags/<tagname>`：删除远程仓库的标签（`:` 前面为空表示推送空值，即删除）
- `git push origin --delete <tagname>`：删除远程仓库的标签（第二种方法）

## Checkout tag

- `git checkout <tagname>`：查看某个标签的文件版本

此时仓库处于 `detacthed HEAD` 状态，所提交的内容将无法访问（除非记下 hash 值），因此通常会先创立新的分支 `git checkout -b <branch> <tagname>`。

# 命令别名（alias）

- `git alias --global alias.<abbr> <op>`：设置操作别名

``` shell
$ git config --global alias.unstage 'reset HEAD --'
$ git reset HEAD -- fileA
# 两个命令等价
```
