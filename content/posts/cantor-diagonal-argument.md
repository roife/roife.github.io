+++
title = "康托的对角线证明"
author = ["roife"]
date = 2022-02-03
tags = ["数理逻辑"]
draft = false
+++

## 对角线证明 {#对角线证明}

对角线证明最初是由康托提出的，用来证明 \\([0, 1]\\) 之间的实数是不可数的。证明如下：

假设实数是可数的，那么可以将其列举。对于同一个数字的不同表示，如 \\(4.\dot{9}\\) 与 \\(5\\)，选择前者。

将所有的数字列举，排成一列。对于第 \\(i\\) 个数字，考虑它的第 \\(i\\) 位。：

\begin{aligned}
& r\_1 = 0 . \underline{\mathbf{5}} 1 0 5 1 1 0 \dots \\\\
& r\_2 = 0 . 4 \underline{\mathbf{1}} 3 2 0 4 3 \dots \\\\
& r\_3 = 0 . 8 2 \underline{\mathbf{4}} 5 0 2 6 \dots \\\\
& r\_4 = 0 . 2 3 3 \underline{\mathbf{0}} 1 2 6 \dots \\\\
& r\_5 = 0 . 4 1 0 7 \underline{\mathbf{2}} 4 6 \dots \\\\
& r\_6 = 0 . 9 9 3 7 8 \underline{\mathbf{3}} 8 \dots \\\\
& r\_7 = 0 . 0 1 0 5 1 3 \underline{\mathbf{5}} \dots \\\\
&\dots
\end{aligned}

现在构造一个实数 \\(r\_k\\)，它的第 \\(i\\) 位与 \\(r\_i\\) 的第 \\(i\\) 位不同，则 \\(r\_k = 0.1325921 \dots\\)

那么对于任意的 \\(r\_i\\)，\\(r\_k \ne r\_i\\)，即 \\(r\_k\\) 不在上面的枚举序列中，因此 \\([0, 1]\\) 之间的实数不可数。
