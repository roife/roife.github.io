---
layout: "post"
title: "「Pro Git」 10 Git Internals"
subtitle: "Git 对象/引用/包文件/引用规范/传输协议/数据维护"
author: "roife"
date: 2020-07-25

tags: ["Pro Git@读书笔记", "读书笔记@Tags", "Git@Linux", "Linux@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 底层命令与上层命令

底层命令指和底层工作有关的命令。

一个典型的 `.git` 目录：

``` shell
$ ls -F1
config # 项目特有配置
description # web 程序使用
HEAD # HEAD 指针
index # 暂存区信息
hooks/ # 钩子
info/ # global exclude 文件
objects/ # 存储数据
refs/ # 存储指针
```

# git 对象

Git 本质上是一个 key-value 的数据库系统，可以在其中插入任何内容，并且返回一个对应的 key，然后根据 key 取出对应的内容。

## blob 对象

- `git hash-object`：将数据保存在 `.git/objects` 返回 SHA-1

  - `-w`：写入数据库
  - `--stdin`：从标准输入读取，不加就要加上路径

``` shell
$ echo 'test content' | git hash-object -w --stdin
d670460b4b4aece5915caf5c68d12f560a9fe3e4
# 此时 objects 目录下就有一个同名文件，记录了这个内容

$ echo 'version 1' > test.txt
$ git hash-object -w test.txt
83baae61804e65cc73a7201a7252750c76066a30
```

此时数据用 blob 对象存储。

- `git cat-file <SHA-1>`：用 SHA-1 取回数据

  - `-p`：自动识别类型
  - `-t`：输出类型

``` shell
$ git cat-file -p d670460b4b4aece5915caf5c68d12f560a9fe3e4 # 取出第一个版本
test content

$ git cat-file -p 83baae61804e65cc73a7201a7252750c76066a30 > test.txt
$ cat test.txt
version 1

$ git cat-file -t 83baae61804e65cc73a7201a7252750c76066a30
blob
```

## 树对象

blob 对象只能存储文件内容，树对象能够存储一些元数据信息。一个树对象包含了一条或多条 tree entry，每个 entry 包含一个指向 blob 或者子树对象的指针，以及相应的元信息。

```shell
$ git cat-file -p master^{tree} # master^{tree} 表示当前 master 分支上最新 commit 指向的树对象
100644 blob a906cb2a4a904a152e80877d4088654daad0c859      README
100644 blob 8f94139338f9404f26296befa88755fc2598c289      Rakefile
040000 tree 99f1a6d12cb4b6f19c8655fca46c3ecf317074e0      lib # lib 是目录，所以它是一个树对象指针，指向另一个树对象

$ git cat-file -p 99f1a6d12cb4b6f19c8655fca46c3ecf317074e0
100644 blob 47c6340d6459e05787f644c2447d2595f5d3a54b      simplegit.rb
```

![data-model-1](/img/in-post/post-pro-git/data-model-1.png){:height="450px" width="450px"}

Git 会从暂存区中提取内容创建树对象，所以我们要先将内容写入暂存区（这里使用底层命令而不用 `git add`）。

- `git update-index`：更新暂存区区域
  + `--add`：将文件添加到暂存区
  + `--cacheinfo <mode> <object> <path>`：文件第一次存入时使用，指定文件模式/SHA-1/文件名（`100644` 表示普通文件，`100755` 表示可执行文件，`120000` 表示符号链接等）
- `git write-tree`：将暂存区内容写入一个树对象

```shell
$ git update-index --add --cacheinfo 100644 83baae61804e65cc73a7201a7252750c76066a30 test.txt

$ git write-tree
d8329fc1cc938780ffdd9f94e0d364e0ea74f579

$ git cat-file -p d8329fc1cc938780ffdd9f94e0d364e0ea74f579 # 查看树对象
100644 blob 83baae61804e65cc73a7201a7252750c76066a30 test.txt

$ git cat-file -t d8329fc1cc938780ffdd9f94e0d364e0ea74f579 # 查看 SHA-1 对应的对象类型
tree
```

- `git read-tree`：将树对象读入暂存区
  + `--prefix=<name>`：将读出的树对象放到 `<name>` 目录下

```shell
$ git read-tree --prefix=bak d8329fc1cc938780ffdd9f94e0d364e0ea74f579

$ git write-tree
3c4e9cd789d88d8d89c1073707c3585e41b0e614

$ git cat-file -p 3c4e9cd789d88d8d89c1073707c3585e41b0e614
040000 tree d8329fc1cc938780ffdd9f94e0d364e0ea74f579     bak
100644 blob 83baae61804e65cc73a7201a7252750c76066a30     test.txt
bak new.txt test.txt
```

## commit 对象

commit 对象可以保存每次 commit 的树对象 SHA-1 值，commit 时间等信息。

- `git commit-tree <SHA-1>`：创建一个 commit 对象，SHA-1 为对应树对象的 SHA-1 值
  + `-p <SHA-1>`：指定对应父 commit

```shell
$ echo 'first commit' | git commit-tree d8329f fdf4fc3344e67ab068f836878b6c4951e3b15f3d # 提供 commit message 与树对象的 SHA-1 值
fdf4fc3344e67ab068f836878b6c4951e3b15f3d

$ git cat-file -p fdf4fc3
tree d8329fc1cc938780ffdd9f94e0d364e0ea74f579
author Scott Chacon <schacon@gmail.com> 1243040974 -0700
committer Scott Chacon <schacon@gmail.com> 1243040974 -0700

first commit

$ echo 'second commit' | git commit-tree 0155eb -p fdf4fc3 cac0cab538b970a37ea1e769cbbde608743bc96d # 在上一个 commit 下创建一个新的 commit
cac0cab538b970a37ea1e769cbbde608743bc96d
```

此时使用 `git log` 就会发现我们已经用底层命令实现了上层命令 `git add/git commit` 的效果。同时在 `.git/objects` 中可以找到各个文件版本对应的内容（文件名为 SHA-1）。

```shell
$ find .git/objects -type f
.git/objects/83/baae61804e65cc73a7201a7252750c76066a30 # test.txt v1
.git/objects/ca/c0cab538b970a37ea1e769cbbde608743bc96d # commit 2
.git/objects/d6/70460b4b4aece5915caf5c68d12f560a9fe3e4 # 'test content'
.git/objects/d8/329fc1cc938780ffdd9f94e0d364e0ea74f579 # tree 1
.git/objects/fd/f4fc3344e67ab068f836878b6c4951e3b15f3d # commit 1
```

可以发现文件夹名为 SHA-1 值的前两位。

## 对象 hash

### blob 对象

blob 对象的格式为 `blob <content length><NUL><content>`。

首先计算头信息。假设文件内容为 `content`，则 `header = "blob \(content.length)\0"`，`length` 为**字节长度**。

然后将二者而二进制拼接起来并计算 SHA-1: `store = header + store`，`hash = sha1(store)`。

接着用 zlib 压缩信息：`zlib_content = zlib(store)`。并将其写入磁盘。其中 hash 的前两位作为目录名，后面部分作为文件名。

### 树对象

树对象的格式为 `tree <content length><NUL>[<file mode> <filename><NUL><item sha>]...<NUL>`，其中 `<item sha>` 为二进制形式的 SHA-1。

首先计算树对象内容：`content = file_mode + filename + "\0" + bin(item_sha)`（如 `"100644 test.txt\0" + bin(sha)`）。

然后拼接得到头信息：`header = header = "tree \(content.length)\0"` 其余步骤和 blob 对象的 hash 一样。

### commit 对象

commit 对象的格式（`content`）如下：

```shell
commit <content length><NUL>tree <tree sha>
parent <parent sha>
[parent <parent sha> if several parents from merges]
author <author name> <author e-mail> <timestamp> <timezone>
committer <author name> <author e-mail> <timestamp> <timezone>

<commit message>
```

计算方法和上述相同。

# Git 引用

## 引用简介

原始的 SHA-1 值很难记忆，所以可以将其存在文件中，并给文件取一个简单的名字作为它的引用。这些引用存在 `.git/refs` 下，共有 `heads`，`tags` 和 `remotes` 三种，分别代表 `HEAD` 引用、标签引用和远程引用。

可以直接将 SHA-1 值写入文件：

```shell
$ echo 1a410efbd13591db07496601ebc7a059dd55cfe9 > .git/refs/heads/master
```

然后就可以用 `master` 代替这个 SHA-1 值。如 `git log master` 等价于 `git log 1a410e`。当然，这是不安全的，最好用底层命令。

- `git update-ref <ref-path> <SHA-1>`：更新 `ref`

```shell
$ git update-ref refs/heads/test cac0ca # 将 test 引用到 cac0ca
```

执行 `git branch <branch>` 时实际上执行了 `git update-ref`。

## HEAD 引用

HEAD 是一个**符号引用**，它不指向某个具体的 commit，而是一个指向另一个引用的指针，通常 HEAD 指向当前所在的分支。如果 HEAD 中是一个 SHA-1 值而不是另一个引用，则此时处于分离 HEAD 状态。

```shell
$ cat .git/HEAD
ref: refs/heads/master
```

使用 `git checkout` 或 `git commit` 时会更改 `HEAD` 文件的内容。

- `git symbolic-ref <ref>`：查看 ref 文件的内容
- `git symbolic-ref <sym-ref> <ref-path>`：将 sym-ref 的指向 ref

```shell
$ git symbolic-ref HEAD refs/heads/test

$ cat .git/HEAD
ref: refs/heads/test
```

## 标签引用

标签对象也是一种 git 对象，类似于 commit 对象包含日期注释等信息。区别在于标签对象指向一个 commit 对象，而不是树对象。标签对象像一个不移动的分支，永远指向同一个 commit 对象（相当于 alias）。

tags 分为 lightweight tags 和 annotated tags。创建 annotated tags 时会生成一个标签对象。

- `git update-ref refs/tags/<version> <commit_id>`：创建 lightweight tag
- `git tag -a <version> <commit_id> -m <message>`

```shell
$ git tag -a v1.1 1a410efbd13591db07496601ebc7a059dd55cfe9 -m 'test tag' # 创建 annotated tag

$ git cat-file -p 9585191f37f7b0fb9444f35a9bf50de191beadc2
object 1a410efbd13591db07496601ebc7a059dd55cfe9 # object 项目指向对应的 commit id
type commit
tag v1.1
tagger Scott Chacon <schacon@gmail.com> Sat May 23 16:48:58 2009 -0700

test tag
```

对于标签对象而言，并不一定要指向某个 commit 对象，可以对任意类型打标签。

```shell
$ git cat-file blob junio-gpg-pub # 指向一个 blob 对象
```

## 远程引用

远程引用保存在 `refs/remote` 下，和分支（`refs/heads`）的区别在于，远程引用是只读的，不能用 `commit` 修改。

Git 记录远程引用的目的在于记录最后一次和服务器通信时远程分支和标签的状态。

# 包文件

在以下三种情况中，Git 会将多个 loose 对象打包成一个包文件（packfile）。
- 当版本库中 loose 对象过多
- 手动执行 `git gc`
- 向远程服务器推送

```shell
$ git gc
Counting objects: 18, done.
Delta compression using up to 8 threads.
Compressing objects: 100% (14/14), done.
Writing objects: 100% (18/18), done.
Total 18 (delta 3), reused 0 (delta 0)
```

打包后查看 `objects` 目录会发现一些对象不见了，同时多出一些新创建的 packfile（`.pack`）和对包文件的索引文件（`.idx`）。

Git 在打包时会查找大小和命名相近的文件，同时只保存相似文件的 diff 信息。一般来说会比较新的版本会存储完整的文件内容，而旧版本作为 diff 的形式保存，因为新版本比旧版本被访问到的概率更大。

- `git verify-pack`：查看已打包的内容

```shell
$ git verify-pack -v .git/objects/pack/pack-978e03944f5c581011e6998cd0e9e30000905586.idx
2431da676938450a4d72e260db3bf7b0f587bbc1 commit 223 155 12
# 省略一部分
b042a60ef7dff760008df33cee372b945b6e884e blob   22054 5799 1463
033b4468fa6b2a9547a70d88d1bbe8bf3f9ed0d5 blob   9 20 7262 1 b042a60ef7dff760008df33cee372b945b6e884e # 引用了 b042a 的信息
```

# 引用规范

引用规范用于服务器分支和本地远程引用（`refs/reomtes`）的映射。

## 引用规范简介

使用 `git remote add` 会在 `.git/config` 中添加一个远程引用，包含远程版本库的名称，URL 以及引用规范。

``` gitconfig
[remote "origin"]
  url = https://github.com/schacon/simplegit-progit
  fetch = +refs/heads/*:refs/remotes/origin/* # 服务器的 refs/heads/ 下面所有引用都写入 refs/remotes/origin/
```

引用规范由一个可选的 `+` 和 `<src>:<dst>` 组成。其中 `<src>`是一个 pattern（但是不能使用部分通配符，如 `*.txt`），代表远程版本库中的引用；`<dst>` 是本地跟踪的位置。`+` 表示即使在不能快进的情况下也要（强制）更新引用。

```shell
# 根据引用规范，以下三者展开后没有区别，都是 refs/remotes/origin/master
$ git log origin/master
$ git log remotes/origin/master
$ git log refs/remotes/origin/master
```

`fetch` 时可以使用引用规范拉取文件。

- `git fetch <remote> <remote_branch>:refs/remotes/<remote>/<branch>`：从服务器的远程分支拉取到本地的跟踪分支

```shell
# 将远程的 master 分支拉取到本地的 mymaster
$ git fetch origin master:refs/remotes/origin/mymaster
```

## 引用规范推送

- `git push <local_branch>:refs/heads/<branch>`：推送本地分支到服务器的分支（`:` 后面的为服务器地址）

## 删除引用

- `$ git push origin :<branch>`：（即把 `src` 清空）
- `git push origin --delete <branch>`：删除引用

# 传输协议

## dumb 协议

dumb 协议的意思是只进行 `get` 操作，但是现在很少使用，因为无法保证安全性和私有化。

1. 拉取 `info/refs`（可以通过 `git update-server-info` 生成），此时获得了一个远程引用和 SHA-1 值列表
2. 拉取 `HEAD`，确定 HEAD 引用
3. 根据 SHA-1 值列表遍历对象。如果是 loose 对象则可以直接获取，否则将得到 404. 此时文件可能在替代版本库或者 packfile 中。
   1. 首先检查替代版本库 `objects/info/http-alternates`
   2. 检查 packfile
      1. 拉取 `objects/info/packs` 得到包文件列表（也是通过 `git update-server-info` 生成）
      2. 拉取包文件索引，查看文件是否在里面
      3. 拉取对应的包文件

## smart 协议

smart 协议可以和服务器进行通信。

### 上传数据

为了上传数据至远端，Git 使用 `send-pack` 和 `receive-pack` 进程。Client 的 `send-pack` 进程连接到 Server 的 `receive-pack` 进程。

#### SSH

1. 本地启动 `send-pack`
2. 尝试 SSH 并在远端执行 `receive-pack`。此时服务端的 `git-receive-pack` 为为它所拥有的每一个引用发送一行响应。
  ```shell
  $ ssh -x git@server "git-receive-pack 'simplegit-progit.git'"
  00a5ca82a6dff817ec66f4437202690a93763949 refs/heads/master report-status delete-refs side-band-64k quiet ofs-delta agent=git/2:2.1.1+github-607-gfba4028 delete-refs
  0000
  # 第一行包含 master 分支和其 SHA-1，以及响应能力（report-status）
  # 每一行以一个四位的 HEX 开始，用于指明本行的长度。（如第一行的 00a5 表示第一行有 165B）
  # 0000 表示结束发送
  ```
3. `send-pack` 判断服务端没有的文件并选择性发送。
  ```shell
  0076ca82a6dff817ec66f44342007202690a93763949 15027957951b64cf874c3557a0f3547bd83b3ff6 \
    refs/heads/master report-status
  006c0000000000000000000000000000000000000000 cdfdb42577e2506715f8cfeacdbabc092bf63e8d \
    refs/heads/experiment
  0000
  # 类似 receive-pack。左边全 0 的 HEX 表示之前没有过这个引用，删除引用时则会显示右边全 0
  ```
4. Client 发送一个包含所有服务端需要的文件的打包
5. Server 返回 `000eunpack ok` 表示成功

#### HTTP(S)

HTTP 的过程大致相同，只有握手阶段有区别。

首先 Get 数据。

```shell
=> GET http://server/simplegit-progit.git/info/refs?service=git-receive-pack
001f# service=git-receive-pack
00ab6c5f0e45abd7832bf23074a333f739977c9e8188 refs/heads/master□report-status delete-refs side-band-64k quiet ofs-delta agent=git/2:2.1.1~vmg-bitmaps-bugaloo-608-g116744e
0000
```

然后客户端再 POST 数据。

```shell
=> POST http://server/simplegit-progit.git/git-receive-pack
```

POST 请求包含了 `send-pack` 的输出以及一个 packfile。然后服务端会返回一个 HTTP 响应。HTTP 协议可能会将这个数据用分块传输编码包裹起来。

### 下载数据

当你在下载数据时，Client 启动 `fetch-pack` 进程，Server 启动 `upload-pack` 进程。

#### SSH

首先 SSH 到服务端。

```shell
$ ssh -x git@server "git-upload-pack 'simplegit-progit.git'"
```

等 `fetch-pack` 连接后，`upload-pack` 会返回内容。

```shell
00dfca82a6dff817ec66f44342007202690a93763949 HEAD□multi_ack thin-pack \
	side-band side-band-64k ofs-delta shallow no-progress include-tag \
	multi_ack_detailed symref=HEAD:refs/heads/master \
	agent=git/2:2.1.1+github-607-gfba4028
003fe2409a098dc3e53539a9028a94b6224db9d6a6b6 refs/heads/master
0000
```

然后 `fetch-pack` 检查有用的对象并且发出请求。

```shell
003cwant ca82a6dff817ec66f44342007202690a93763949 ofs-delta # 需要的对象
0032have 085bb3bcb608e1e8451d4b2432f8ecbe6306e7e7 # 拥有的对象
0009done # 完成，通知服务端开始发送
0000
```

#### HTTP(S)

HTTP(S) 需要两次握手。

首先向和 dump 协议中相同的端点发送 GET 请求（类似于 SSH 的 `git-upload-pack`）。

```shell
=> GET $GIT_URL/info/refs?service=git-upload-pack
001e# service=git-upload-pack
00e7ca82a6dff817ec66f44342007202690a93763949 HEAD multi_ack thin-pack \
    side-band side-band-64k ofs-delta shallow no-progress include-tag \
    multi_ack_detailed no-done symref=HEAD:refs/heads/master \
    agent=git/2:2.1.1+github-607-gfba4028
003fca82a6dff817ec66f44342007202690a93763949 refs/heads/master
0000
```

然后 POST 数据。这个请求的响应包含了所需要的包文件，并指明成功或失败。

```shell
=> POST $GIT_URL/git-upload-pack HTTP/1.0
0032want 0a53e9ddeaddad63ad106860237bbf53411d11a7
0032have 441b40d833fdfa93eb2908e52742248faf0ee993
0000
```

# 维护与数据恢复

## 维护

Git 会自动执行 `auto gc`，包文件太多时可以将其合并。通过修改 `gc.auto` 与 `gc.autopacklimit` 可以修改发生 gc 的阈值。

- `git gc --auto`：手动执行自动垃圾回收

类似的，一些引用也会被打包到 `.git/packed-refs`。但是更新引用后并不会更新 `packed-refs`，只会在 `refs/heads` 中创建新文件。只有在 `refs/heads` 中找不到时才会到 `packed-refs` 中寻找。（类似于一个 cache 关系）

```shell
$ cat .git/packed-refs
# pack-refs with: peeled fully-peeled
cac0cab538b970a37ea1e769cbbde608743bc96d refs/heads/experiment
ab1afef80fac8e34258ff41fc1b867c702daa24b refs/heads/master
cac0cab538b970a37ea1e769cbbde608743bc96d refs/tags/v1.0
9585191f37f7b0fb9444f35a9bf50de191beadc2 refs/tags/v1.1
^1a410efbd13591db07496601ebc7a059dd55cfe9 # ^ 开头表示 annotated tag
```

## 数据恢复

- `git reflog`：显示每一次改变 HEAD 时的 SHA-1

reflog 会在执行 `git update-ref` 时更新（所以使用 `update-ref` 比直接向文件中写入 SHA-1 值安全）。

```shell
$ git reflog
1a410ef HEAD@{0}: reset: moving to 1a410ef
ab1afef HEAD@{1}: commit: modified repo.rb a bit
484a592 HEAD@{2}: commit: added repo.rb
```

- `git log -g`：用标准日志的格式输出引用日志（比 `reflog` 更详细）

```shell
$ git log -g
commit 1a410efbd13591db07496601ebc7a059dd55cfe9
Reflog: HEAD@{0} (Scott Chacon <schacon@gmail.com>)
Reflog message: updating HEAD
Author: Scott Chacon <schacon@gmail.com>
Date: Fri May 22 18:22:37 2009 -0700

        third commit

commit ab1afef80fac8e34258ff41fc1b867c702daa24b
Reflog: HEAD@{1} (Scott Chacon <schacon@gmail.com>)
Reflog message: updating HEAD
Author: Scott Chacon <schacon@gmail.com>
Date: Fri May 22 18:15:24 2009 -0700
        modified repo.rb a bit
```

但是如果发现 `reflog` 里面也没有发现需要的分支，则要用 `git fsck` 解决。其中 `dangling commit` 表示丢失的提交。

- `git fsck --full`：查看没有被其他对象指向的对象

```shell
$ git fsck --full
Checking object directories: 100% (256/256), done.
Checking objects: 100% (18/18), done.
dangling blob d670460b4b4aece5915caf5c68d12f560a9fe3e4
dangling commit ab1afef80fac8e34258ff41fc1b867c702daa24b # 丢失的提交
dangling tree aea790b9a58f6cf6f2804eeac9f0abbe9631e4c9
dangling blob 7108f7ecb345ee9d0084193f147cdad4d2998293
```

## 移除对象

加入有人不小心向版本库中添加了非常大的文件，然后又删除了它，导致这个文件在版本库中留下了记录，此时可以将其从历史中删除。

**注意，下面的操作都是破坏性的！**

这个过程需要重写添加大文件后的每一个 commit，并且需要其他 contributor 的配合，将其工作 rebase 到新的版本库上。

- `git count-objects`：查看占用空间

```shell
$ git count-objects -v
count: 7
size: 32
in-pack: 17
packs: 1
size-pack: 4868 # 单位为 KB
prune-packable: 0
garbage: 0
size-garbage: 0
```

1. 找到这个文件的对象
   - `git verify-pack`：检查 packfile

   ```shell
   $ git verify-pack -v .git/objects/pack/pack-29...69.idx | sort -k 3 -n | tail -3
   dadf7258d699da2c8d89b09ef6670edb7d5f91b4 commit 229 159 12
   033b4468fa6b2a9547a70d88d1bbe8bf3f9ed0d5 blob   22044 5792 4977696
   82c99a3e86bb1267b236a4b6eff7868d97489af1 blob   4975916 4976258 1438 # 找到文件，大约 5MB
   ```

2. 找到具体的文件
   - `git rev-list`：倒序输出所有对象
     + `--objects`：列出对象的 SHA-1 与路径

   ```shell
   $ git rev-list --objects --all | grep 82c99a3
   82c99a3e86bb1267b236a4b6eff7868d97489af1 git.tgz
   ```

3. 找到对应的 commit
  ```shell
  $ git log --oneline --branches -- git.tgz
  dadf725 oops - removed large tarball
  7b30847 add git tarball
  ```

4. 重写历史
  ```shell
  # index-filter 不会修改 checkout 的文件，会修改暂存区或索引中的文件
  $ git filter-branch --index-filter \
      'git rm --cached --ignore-unmatch git.tbz2' -- 6df7640^..
  Rewrite 6df764092f3e7c8f5f94cbe08ee5cf42e92a0289 (1/2) rm 'git.tbz2'
  Rewrite da3f30d019005479c99eb4c3406225613985a1db (2/2)
  Ref 'refs/heads/master' was rewritten
  ```

5. 重新打包
  ```shell
  # 清理引用日志和数据库并重新打包
  $ rm -Rf .git/refs/original
  $ rm -Rf .git/logs/
  $ git gc
  ```

6. 完全移除对象
  ```shell
  $ git prune --expire now
  ```
