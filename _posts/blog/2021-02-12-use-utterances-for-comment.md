---
layout: "post"
title: "使用 Utterances 作为静态博客的评论插件"
subtitle: "更轻量安全的评论插件"
author: "roife"
date: 2021-02-12

tags: ["博客搭建@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

[utterances](https://utteranc.es) 是一款基于 GitHub issues 的开源评论插件，类似于 Gitalk，支持 markdown。

# 为什么不用 Disqus 与 Gitalk

首先 Disqus 的 UI 过于冗余了，而且免费使用有广告，看起来不舒服。

Gitalk 等同样是基于 GitHub issues 的评论插件存在**安全性问题**。这些评论插件都是通过 OAuth 取得操作 issues 的权限，因此必须将 clientID 和 clientSecret 硬编码入 commit，而这个操作会将二者直接暴露出去。尽管获得对 repos 的操作权限还需要授权 Token，但是这个可以通过反代 GitHub API 等手段拿到。由于 GitHub 在权限粒度上并没有进一步细分（也就是说不能只操作 issues），所以一旦拿到 Token，对方就可以删光你的 public repos，因此使用它们的风险是非常高的。

而 Utterances 通过 GitHub App 实现，可以只对 issues 进行授权，因此没有了安全性风险。唯一要担心的问题是 Utterances 的开发者跑路（因为 Utterances 仍然需要服务端设施），但即使如此 issues 中的评论也不会消失，所以也不用担心数据丢失，大不了到时候将数据导出就好了。

Utterances 另一个好处就是不需要初始化，而 Gitalk 等评论插件都是需要作者手动初始化的。

当然，Utterances 也有缺点，就是加载可能会比较慢，这一点见仁见智，至少我在使用上没有体验出区别。

~~话是这么说，真的会有人来我的博客写评论吗~~

# 安装 Utterances

## 申请 GitHub App

首先保证自己的博客是 public 仓库。

打开 [utterances - GitHub App](https://github.com/apps/utterances) 点击 `Install` 进入安装页面。

在打开的页面中选择 `Only select repositories`，并在下拉框中选择自己的博客仓库（比如我就是 `roife/roife.github.io`，也可以安装到其他仓库），然后点击 `Install`。

如图（我已经安装过了，所以这里是设置界面，但是大同小异）：

![utterances-installation](/img/in-post/post-use-utterances-for-comment/utterances-installation.png){:height="700px" width="700px"}

## 配置

其实 Utterances 已经在我们的博客上配置好了，这一步是为了生成个性化的 HTML 配置插入博客。

安装完成后就会自动跳转到配置页面，也可以手动打开 [Utterances](https://utteranc.es)。

在 repository 中填入仓库名称，比如我就是 `roife/roife.github.io`，注意格式，不要忘记用户名。

`Blog Post ↔️ Issue Mapping` 表示 issues 标题和博客 posts 的映射关系，我选择默认的第一项 `Issue title contains page pathname`。

`Issue Label` 表示用于评论的 issues 要不要打上 label，这一项是可选的。我选择为这些 issues 打上 `Comment`。

最后一项是 `Theme` 根据自己的喜好选择即可。

![utterances-configuration](/img/in-post/post-use-utterances-for-comment/utterances-configuration.png){:height="700px" width="700px"}

然后就会生成一段对应选项的 HTML 配置，应该是类似于这样的：

```html
<script src="https://utteranc.es/client.js"
        repo="[ENTER REPO HERE]"
        issue-term="pathname"
        theme="github-light"
        crossorigin="anonymous"
        async>
</script>
```

直接将它插入到你的博客中对应的位置即可。

# 后记

如果之前申请了 Gitalk 或者类似的评论插件，不要忘了取消 Gitalk 之前的授权，因为在 log 里面还能看到 clientSecret。

~~博客系统换了一款又一款，但是到现在几乎一条评论都没有~~