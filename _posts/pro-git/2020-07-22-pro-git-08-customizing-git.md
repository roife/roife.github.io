---
layout: "post"
title: "「Pro Git」 08 Customizing Git"
subtitle: "配置 Git"
author: "roife"
date: 2020-07-22

tags: ["Pro Git@读书笔记", "读书笔记@Tags", "Git@Linux", "Linux@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 客户端常用配置

- `core.editor`：编辑器
- `commit.template`：commit 模板
- `user.signingkey`：密钥 ID
- `core.excludesfile`：全局生效的 gitignore
- `help.autocorrect`：自动纠正错误命令
- `core.autocrlf`：设置为 true，则自动在 CR 和 LF 之间转换；设置为 input，则自动转换为 LF
- `core.whitespace`：自动检查空格问题，在不需要的选项前加 `-` ，如 `$ git config --global core.whitespace trailing-space,-space-before-tab`
  - `blank-at-eol`：查找行尾的空格
  - `blank-at-eof`：盯住文件底部的空行
  - `space-before-tab`：警惕行头 tab 前面的空格
  - `indent-with-non-tab`：揪出以空格而非 tab 开头的行（可以用 tabwidth 选项控制它）
  - `tab-in-indent`：监视在行头表示缩进的 tab
  - `cr-at-eol`：告诉 Git 忽略行尾的回车

可以在 `git apply` 和 `git fix` 的时候设置 `--whitespace=warn` 或者
`--whitespace=fix` 来警告和自动修复

# 属性

`.gitattributes` 文件的配置。

可以用 `core.attributesFile` 配置全局的 attributes 文件。

## 二进制文件

### 识别二进制文件

在 `.gitattributes` 中设置

``` gitattributes
*.pbxproj binary
```

`git show` 和 `git diff` 不会检查二进制文件。

### 比较二进制文件

在 `.gitattributes` 中设置

``` gitattributes
*.png diff=exif
*.docx diff=word # exif 和 word 为自己设置
```

然后配置 config

``` shell
$ git config diff.exif.textconv exiftool
$ git config diff.word.textconv docx2txt # docx2txt 要用脚本封装：docx2txt.pl "$1" -
```

## 关键字展开

在 `.gitattributes` 中设置

``` gitattributes
date*.txt filter=indent
```

然后配置：

``` shell
$ git config --global filter.indent.clean indent
$ git config --global filter.indent.smudge cat
```

就会暂存时触发 indent，在 checkout 时触发 cat。

## 导出版本库

在 `.gitattributes` 中设置 `export-ignore` 可以在导出时忽略一些文件

``` gitattributes
test/ export-ignore # 忽略 test 目录
```

## 合并策略

在 `.gitattributes` 中设置

``` gitattributes
database.xml merge=ours
```
