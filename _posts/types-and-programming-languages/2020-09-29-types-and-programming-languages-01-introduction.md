---
layout: "post"
title: "「TAPL」 01 Introduction"
subtitle: "介绍"
author: "roife"
date: 2020-09-29

tags: ["Types and Programming Languages@Books@Series", "PKU - 编程语言的设计原理@Courses@Series", "程序语言理论@Tags@Tags", "类型系统@Tags@Tags"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Types in CS

> A **type system** is a tractable syntactic method for proving the absence of certain (bad) program behaviors by **classifying** phrases according to the kinds of values they compute.

- Tools for program reasoning (tractable and syntactic)
- Fully automatic (and efficient)
- Classification of terms
- Static approximation (Rice’s theorem)
- Proving the absence rather than presence

# Advantages

- Detecting Errors
- Abstraction
- Documentation
- Language Safety (A safe language is one that protects its own abstractions.)
- Efficiency (Removal of dynamic checking; smart code-generation)

# Type Systems and Languages Design

> Language design should go hand-in-hand with type system design

- 不事先设计类型系统的语言可能会添加一些难以分析的特性
- typed languages 中一般包含 type annotations, 这会影响其他语法的设计
