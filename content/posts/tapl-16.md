+++
title = "[TaPL] 16 Metatheory of Subtyping"
author = ["roife"]
date = 2023-07-07
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论", "程序语义", "subtyping"]
draft = false
+++

前面使用的 subtyping rules 并不适合实际实现，因为它们并不是自底向上构建的，主要问题在于下面两个规则：

-   `T-Sub`

    \\[\dfrac{\Gamma \vdash t : S \quad S <: T}{\Gamma \vdash t : T} \tag{T-Sub}\\]

    其他大部分 typing rules 都是对于某个特殊结构进行类型推导（syntax-directed），而 `T-Sub` 的推导对象是一个 metavar \\(t\\)，因此这条规则总可以对一个 term 使用，且目标类型 \\(T\\) 是未知的，需要程序来决定使用的时机。

-   `S-Trans`

    \\[\dfrac{S <: U \quad U <: T}{S <: T} \tag{S-Trans}\\]

    `S-Trans` 也有类似的问题。并且除此之外，`S-Trans` 在使用时需要程序自己推理出一个中间变量 \\(U\\)，这对程序来说是很困难的。

-   `S-Refl`

    \\[S <: S \tag{S-Refl}\\]

    `S-Refl` 中没有假设条件，因此这一条也是在任何时候都可以使用的，它也不是 syntax-directed 的。

因此本章使用新的 typing rules 替代原有的规则（称为 declarative relation），称为 **algorithmic subtyping** 和 **algorithmic typing**，其推断过程是 syntax-directed 的。然后会证明这些规则和原有规则是等价的（即可以互相推导）。


## Algorithmic Subtyping {#algorithmic-subtyping}

本章将介绍一个算法，用于判断一个类型是否是另一个类型的 subtype。这个算法是 syntax-directed 的，即对于每个类型都有一个对应的规则。


### Definition and equivalence {#definition-and-equivalence}

Typechecker 在判断 \\(S <: T\\) 时会判断 \\((S, T)\\) 是否包含在 \\(\mapsto S <: T\\)（称为 \\(S\\) is algorithmically a subtype of \\(T\\)，并且是 syntax-directed 的） 中。Algorithmic subtyping relation 里中去掉了 `S-Trans` 和 `S-Refl` 这两条规则，并让这两条规则直接蕴含在其他具体的规则中。

首先，对于之前 record types 定义了三条规则，分别是 `S-RcdDepth`，`S-RcdWidth` 和 `S-RcdPerm`。这三条规则在使用时往往需要配合 `S-Trans` 使用，因此这里将这三条规则合并为 `S-Rcd`。

\\[\dfrac{\\{l\_{i}^{i \in 1 \dots n}\\} \subseteq \\{k\_{j}^{j \in 1 \dots m}\\} \quad k\_j = l\_i \rightarrow S\_j <: T\_i}{\\{k\_{j} : S\_j^{j \in 1 \dots m}\\} <: \\{l\_{i} : T\_i^{i \in 1 \dots n}\\} } \tag{S-Rcd}\\]

{{< figure src="/img/in-post/post-tapl/16-1-subtype-relation-with-records.png" caption="<span class=\"figure-number\">Figure 1: </span>Subtype relation with records" >}}

<div class="lemma">

If \\(S <: T\\) is derivable from the subtyping rules including `S-RcdDepth`, `S-RcdWidth`, and `S-RcdPerm` (but not `S-Rcd`), then it can also be derived using `S-Rcd` (and not `S-RcdDepth`, `S-Rcd-Width`, or `S-Rcd-Perm`), and vice versa.

</div>

<div class="lemma">

下面证明 `S-Refl` 和 `S-Trans` 在上面的规则中（即仅包含函数和 record type 的 subtyping 系统）都是不必要的。

1.  \\(S <: S\\) can be derived for every type \\(S\\) without using `S-Refl`.
2.  If \\(S <: T\\) is derivable, then it can be derived without using `S-Trans`.

</div>

<div class="proof">

只要证明 `S-Refl` 和 `S-Trans` 都可以用其他规则表示。

第一个 lemma 直接对 \\(S\\) 的推导进行归纳。对于不同的类型使用的 `S-Refl` 分别使用 `S-Top`，`S-Arrow` 和 `S-Rcd` 替代。如果增加了更多的 base type，则需要分别加入对应的 `S-Base`（例如 `Bool <: Bool`）。

下面主要证明第二个 lemma。由于 `S-Trans` 的假设都是 subtyping 规则，因此只需要考虑 `S-*`。对 derivations 的**大小**进行归纳，假设比当前小的都成立。如果 derivations 中应用的最后一条规则不是 `S-Trans`，那么根据归纳假设，前面的部分也可以不用 `S-Trans`，成立。

因此下面考虑最后一条规则是 `S-Trans` 的情况——即存在两个 sub-derivations \\(S <: U\\) 和 \\(U <: T\\)，并且两个 subderivations 中都没有用到 `S-Trans`。讨论两个 sub-derivations 的最后一条规则：

-   Any + `S-Top` ：直接替换成 `S-Top`
-   `S-Top` + Any：则 `U = Top`，则 `T` 也是 `Top`，那么右侧一定是 `S-Top`，归于第一条
-   `S-Arrow` + `S-Arrow`：

    \begin{aligned}
    & S = S\_1 \rightarrow S\_2 \\\\
    & U = U\_1 \rightarrow U\_2 \\\\
    & T = T\_1 \rightarrow T\_2
    \end{aligned}

    \begin{aligned}
    & U\_1 <:S\_1 & S\_2 <:U\_2 \\\\
    & T\_1 <:U\_1 & U\_2 <:T\_2
    \end{aligned}

    即

    \\[
      \dfrac{
        \dfrac{\dfrac{...}{U\_1 <:S\_1} \quad \dfrac{...}{S\_2 <:U\_2}}{S <: U} (\operatorname{\mathrm{S-Arrow}})
        \quad
        \dfrac{\dfrac{...}{T\_1 <:U\_1} \quad \dfrac{...}{U\_2 <:T\_2}}{U <: T}(\operatorname{\mathrm{S-Arrow}})
      }
      {S <: T} (\operatorname{\mathrm{S-Trans}})
      \\]

    这一段可以替换为等价的：

    \\[
      \dfrac{
        \dfrac{
          \dfrac{...}{U\_1 <: S\_1} \quad
          \dfrac{...}{T\_1 <:U\_1}
        }{T\_1 <: S\_1} (\operatorname{\mathrm{S-Trans}})
        \quad
        \dfrac{\dfrac{...}{S\_2 <:U\_2} \quad \dfrac{...}{U\_2 <:T\_2}}{S\_2 <: T\_2}(\operatorname{\mathrm{S-Trans}})
      }
      {S <: T} (\operatorname{\mathrm{S-Arrow}})
      \\]

    根据归纳假设，两个 sub-derivations 也可以被改写为完全不需要 `S-Trans` 的形式。因此在整个证明中可以完全不用到 `S-Trans`，证毕。

-   `S-Rcd` + `S-Rcd`：类似 `S-Arrow` / `S-Arrow`
-   `S-Arrow` + `S-Rcd` 和 `S-Rcd` / `S-Arrow`：不可能

</div>

<div class="definition">

**(algorithmic subtyping relation)**

The algorithmic subtyping relation is the least relation on types closed under the rules in the figure below.

{{< figure src="/img/in-post/post-tapl/16-2-algorithmic-subtyping.png" caption="<span class=\"figure-number\">Figure 2: </span>Algorithmic subtyping" >}}

</div>

Algorithmic subtyping relation 和原先的 subtyping relation 是等价的：

<div class="theorem">

**(Soundness and completeness)**

\\(S <: T \iff \mapsto S <: T\\)

</div>

<div class="proof">

根据上面的两个引理通过归纳易证。

</div>


### Implementation {#implementation}

根据上面的规则，可以实现一个算法来判断 \\(S <: T\\) 是否成立。这个算法是 syntax-directed 的：

<div class="pseudocode">

\begin{algorithm}
  \caption{Algorithmic Subtyping}
  \begin{algorithmic}
    \procedure{subtype}{$S, T$}
      \if{$T = \operatorname{\mathtt{Top}}$}
        \return{true}
      \elseif{$S = S\_1 \rightarrow S\_2 \land T = T\_1 \rightarrow T\_2$}
        \return{subtype($T\_1, S\_1$) $\land$ subtype($S\_2, T\_2$)}
      \elseif{$S = \\{k\_j : S\_j^{j \in 1 \dots m}\\} \land T = \\{l\_i : T\_i^{i \in 1 \dots n}\\}$}
        \return{$\\{l\_i^{i \in 1 \dots n}\\} \subseteq \\{k\_j^{j \in 1 \dots m}\\} \land (\forall i, \exists j, k\_j = l\_i$ $\land$ subtype($S\_j, T\_i$))}
      \else
        \return{false}
      \endif
    \endprocedure
  \end{algorithmic}
\end{algorithm}

</div>


### Termination {#termination}

<div class="proposition">

**(Termination)**

If \\(\mapsto S <: T\\) is derivable, then \\(\operatorname{\mathrm{subtype}}(S, T)\\) will return **true**.

If not, then subtype(S, T) will return **false**.

</div>

<div class="proof">

因为算法是 syntax-directed 的，对 type derivations 的过程进行归纳即可就能证明正确细节。

下面只要证明算法会终止。观察算法可以发现，每次进行递归时，类型的 size 都会单调减小，因此算法一定会终止。

</div>

Soundness, completeness and termination 共同保证了这个算法是 decidable 的。采用 algorithmic definition 作为定义虽然看似节省时间，但实际上不适合进行证明，因此这里优先叙述 declarative definition。


## Algorithmic Typing {#algorithmic-typing}


### Definition {#definition}

在 algorithmic subtyping 中，我们去掉了 `S-Trans` 和 `S-Refl`，并且证明了这两条规则是不必要的。在本章中，我们会继续去掉 `T-Sub`。

考虑在类型推导中使用 `T-Sub` 的场景，下面首先证明一个 lemma：当类型推导中使用了 `T-Sub` 时，总可以将用到它的推导“下移”。

考虑在 derivations 中 `T-Sub` 后紧跟的规则（`T-Var` 可以被直接排除）：

-   `T-Abs`

    \\[
      \dfrac{
        \dfrac{
          \dfrac{...}{\Gamma, x:S\_1 \vdash s\_2 : S\_2}
          \quad
          \dfrac{...}{S\_2 <: T\_2}
        }{\Gamma, x:S\_1 \vdash s\_2 : T\_2} (\operatorname{\mathrm{T-Sub}})
      }
      {\Gamma \vdash \lambda x:S\_1 . s\_2 : S\_1 \rightarrow T\_2}(\operatorname{\mathrm{T-Abs}})
      \\]

    由于最后一条规则是 `T-Abs`，那么 `T-Sub` 一定是对函数类型的部件（参数类型或返回类型）使用。而这种情况可以直接使用 `S-Arrow` 拼凑出 subtyping 关系，然后再使用 `T-Sub`。

    \\[\dfrac{
        \dfrac{
          \dfrac{...}{\Gamma, x:S\_1 \vdash s\_2 : S\_2}
        }{\Gamma \vdash \lambda x:S\_1 . s\_2 : S\_1 \to S\_2} (\operatorname{\mathrm{T-Abs}})
        \quad
        \dfrac{
          \dfrac{...}{S\_1 <: S\_1}(\operatorname{\mathrm{S-Refl}})
          \quad
          \dfrac{...}{S\_2 <: T\_2}
        }{S\_1 \to S\_2 <: S\_1 \to T\_2} (\operatorname{\mathrm{S-Arrow}})
      }
      {\Gamma \vdash \lambda x:S\_1 . s\_2 : S\_1 \to T\_2}
      \\]

-   `T-App`

    在 `T-App` 前使用 `T-Sub` 有两种可能的情况：对函数使用 `T-Sub` 或者对参数使用 `T-Sub`。

    -   对函数使用 `T-Sub`

        \\[
              \dfrac{
                \dfrac{
                  \dfrac{...}{\Gamma \vdash s\_{1} : S\_{11} \rightarrow S\_{12}}
                  \quad
                  \dfrac{...}{S\_{11} \rightarrow S\_{12} <: T\_{11} \rightarrow T\_{12}}     (\operatorname{\mathrm{S-Arrow}})
                }{
                  \Gamma \vdash s\_1 : T\_{11} \rightarrow T\_{12}
                } (\operatorname{\mathrm{T-Sub}})
                \quad
                \dfrac{...}{\Gamma \vdash s\_{2} : T\_{11}}
              }{
                \Gamma \vdash s\_{1}\ s\_{2} : T\_{12}
              } (\operatorname{\mathrm{T-APP}})
            \\]

        这里值得注意的是使用了 `S-Arrow` 的这个 sub-derivations，根据上一节的讨论可以知道在 derivations 中总可以将 `S-Refl` 和 `S-Trans` 去掉，因此这里假设直接使用了 `S-Arrow`：

        \\[
              \dfrac{
                \dfrac{
                  \dfrac{...}{\Gamma \vdash s\_{1} : S\_{11} \rightarrow S\_{12}}
                  \quad
                  \dfrac{
                    \dfrac{...}{T\_{11} <: S\_{11}}
                    \quad
                    \dfrac{...}{S\_{12} <: T\_{12}}
                  }{S\_{11} \rightarrow S\_{12} <: T\_{11} \rightarrow T\_{12}} (\operatorname{\mathrm{S-Arrow}})
                }{
                  \Gamma \vdash s\_1 : T\_{11} \rightarrow T\_{12}
                } (\operatorname{\mathrm{T-Sub}})
                \quad
                \dfrac{...}{\Gamma \vdash s\_{2} : T\_{11}}
              }{
                \Gamma \vdash s\_{1}\ s\_{2} : T\_{12}
              } (\operatorname{\mathrm{T-APP}})
            \\]

        当对函数的结果类型使用 `T-Sub` 时，可以先使用 `T-App` 再使用 `T-Sub`；对函数的参数类型使用 `T-Sub` 时，可以将其变成对 `T-App` 的参数使用 `T-Sub`，但是注意到这时会多出一个 `T-Sub`，仍然处于 `T-App` 的上方。实际上被挪下来的 `T-Sub` 只是对结果类型使用的规则，对参数类型使用的 `T-Sub` **无法被挪下来**。

        \\[
            \dfrac{
              \dfrac{
                \dfrac{...}{\Gamma \vdash s\_1 : S\_{11} \rightarrow S\_{12}}
                \quad
                \dfrac{
                  \dfrac{...}{\Gamma \vdash s\_2 : T\_{11}}
                  \quad
                  \dfrac{...}{T\_{11} <: S\_{11}}
                }{\Gamma \vdash s\_{2} : S\_{11}} (\operatorname{\mathrm{T-Sub}})
              }{\Gamma \vdash s\_{1}\ s\_{2} : T\_{11}} (\operatorname{\mathrm{T-App}})
              \quad
              \dfrac{...}{\Gamma \vdash s\_2 : T\_{11}}
            }
            {\Gamma \vdash s\_1\ s\_2 : T\_{12}} (\operatorname{\mathrm{T-Sub}})
            \\]

    -   对参数使用 `T-Sub`

        \\[
            \dfrac{
              \dfrac{
                ...
              }{\Gamma \vdash s\_1 : T\_{11} \rightarrow T\_{12}}
              \quad
              \dfrac{
                \dfrac{
                  ...
                }{\Gamma \vdash s\_2 : T\_2}
                \quad
                \dfrac{
                  ...
                }{T\_2 <: T\_{11}}
              }{\Gamma \vdash s\_2 : T\_{11}} \ (\operatorname{\mathrm{T-Sub}})
            }
            {\Gamma \vdash s\_1\ s\_2 : T\_{12}} \ (\operatorname{\mathrm{T-App}})
            \\]

        类似前面的结论，这里的 `T-Sub` 不能被挪下来：

        \\[
            \dfrac{
            \dfrac{
              \dfrac{
                ...
              }{\Gamma \vdash s\_1 : T\_{11} \rightarrow T\_{12}}
              \quad
              \dfrac{
                \dfrac{
                  ...
                }{T\_2 <: T\_{11}}
                \quad
                \dfrac{
                  ...
                }{T\_{12} <: T\_{12}} (\operatorname{\mathrm{S-Refl}})
              }{T\_{11} \rightarrow T\_{12} <: T\_2 \rightarrow T\_{12}} (\operatorname{\mathrm{S-Arrow}})
            }
            {\Gamma \vdash s\_1 : T\_2 \rightarrow T\_{12}} (\operatorname{\mathrm{T-Sub}})
            \quad
            \dfrac{
              ...
            }{\Gamma \vdash s\_2 : T\_2}
            }{\Gamma \vdash s\_1\ s\_2 : T\_{12}} (\operatorname{\mathrm{T-App}})
            \\]

-   `T-Sub`

    \\[
        \dfrac{
          \dfrac{
            \dfrac{...}{\Gamma \vdash s : S} \quad
            \dfrac{...}{S <: U}
          }{\Gamma \vdash s : U} (\operatorname{\mathrm{T-Sub}})
          \quad
          \dfrac{...}{U <: T}
        }
        {\Gamma \vdash s : T} (\operatorname{\mathrm{T-Sub}})
      \\]

    连续的 `T-Sub` 可以用 `S-Trans` 进行合并；并且根据前面的讨论，`S-Trans` 也可以被消去。

    \\[
        \dfrac{
        \dfrac{...}{\Gamma \vdash s : S}
        \quad
          \dfrac{
            \dfrac{...}{S <: U}
            \quad
            \dfrac{...}{U <: T}
          }{\Gamma \vdash s : T} (\operatorname{\mathrm{S-Trans}})
        }
        {\Gamma \vdash s : T} (\operatorname{\mathrm{T-Sub}})
      \\]

<!--listend-->

-   `T-Rcd`

    \\[
      \dfrac{
        \dfrac{...}{\Gamma \vdash t\_{i} : T\_{i}^{i \in 1 \dots k-1, k+1 \dots n}}
        \quad
        \dfrac{
          \dfrac{...}{\Gamma \vdash t\_{k} : S}
          \quad
          \dfrac{...}{S <: T\_{k}}
        }{\Gamma \vdash t\_{k} : T\_{k}} (\operatorname{\mathrm{T-Sub}})
      }{
        \Gamma \vdash \\{l\_{i} = t\_{i}^{i \in 1 \dots n}\\} : \\{l\_{i} : T\_{i}^{i \in 1 \dots n}\\}
      } \operatorname{\mathrm{(T-Rcd)}}
      \\]

    利用 `S-Rcd`，这里的 `T-Sub` 可以被挪下来：

    为了方便，这里记 \\(\mathcal{T}\_k = 1 \dots k-1, k+1 \dots n\\)

    \\[
      \dfrac{
        \dfrac{
            \dfrac{...}{\Gamma \vdash t\_{i} : T\_{i}^{i \in \mathcal{T}\_k}}
            \quad
            \dfrac{...}{\Gamma \vdash t\_{k} : S}
        }{
            \Gamma \vdash \\{l\_{i} = t\_{i}^{i \in 1 \dots n}\\} : \\{l\_{i} <: T\_{i}^{i \in \mathcal{T}\_k}, l\_k <: S\\}
        } \operatorname{\mathrm{(T-Rcd)}}
        \quad
        \dfrac{
          \dfrac{...}{S <: T\_{k}}
          \quad
          \dfrac{}{T\_{i}^{i \in \mathcal{T}\_k} <: T\_{i}^{i \in \mathcal{T}\_k}} (\operatorname{\mathrm{S-Refl}})
        }{
          \Gamma \vdash \\{l\_{j} : T\_j^{j \in \mathcal{T}\_k}, l\_{k} : S\\} <: \\{l\_{i} : T\_i^{i \in 1 \dots n}\\}
        } \operatorname{\mathrm{(S-Rcd)}}
      }{
        \Gamma \vdash \\{l\_{i} = t\_{i}^{i \in 1 \dots n}\\} : \\{l\_{i} : T\_{i}^{i \in 1 \dots n}\\}
      } \operatorname{\mathrm{(S-Sub)}}
      \\]

-   `T-Proj`

    \\[
      \dfrac{
        \dfrac{
          \dfrac{...}{\Gamma \vdash t\_{} : \\{l\_i : S\_i^{1 \dots n}\\}}
          \quad
          \dfrac{...}{\\{l\_i : S\_i^{1 \dots n}\\} <: \\{l\_i : T\_i^{1 \dots n}\\}}
        }{\Gamma \vdash t\_{} : \\{l\_i : T\_i^{1 \dots n}\\}} (\operatorname{\mathrm{T-Sub}})
      }{
        \Gamma \vdash t.l\_j : T\_j
      } \operatorname{\mathrm{(T-Proj)}}
      \\]

    类似的，这里的 `T-Sub` 也可以被挪下来：

    \\[
      \dfrac{
        \dfrac{
          \dfrac{...}{\Gamma \vdash t\_{} : \\{l\_i : S\_i^{1 \dots n}\\}}
        }{\Gamma \vdash t.l\_j : S\_j} \operatorname{\mathrm{(T-Proj)}}
        \quad
        \dfrac{...}{\\{l\_i : S\_i^{1 \dots n}\\} <: \\{l\_i : T\_i^{1 \dots n}\\}}
      }{
        \Gamma \vdash T.l\_j : T\_j
      } (\operatorname{\mathrm{T-Sub}})
      \\]

综合上面的讨论，可以发现经过变换后，`T-Sub` 只会出现在两个位置上：

-   对 application 的参数使用（即 `t1 t2` 中对 `t2` 使用），使其与 abstraction 的参数类型相匹配：为了解决这个问题，我们可以将 `T-App` 替换成一个包含 `T-Sub` 的更强的版本：

    \\[\dfrac{\Gamma \vdash t\_{1} : T\_{11} \rightarrow T\_{12} \quad \Gamma \vdash t\_2 : T\_2 \quad T\_2 <: T\_{11}} {\Gamma \vdash t\_1\ t\_2 : T\_{12}}\\]

    这条规则是 syntax-directed 的。

-   对 type derivations 最后的结果使用：这种情况发生在 derivations 的末尾，因此不影响中间的类型推导，只是最后的类型会更“小”

{{< figure src="/img/in-post/post-tapl/16-3-algorithmic-typing.png" caption="<span class=\"figure-number\">Figure 3: </span>Algorithmic typing" >}}

<div class="definition">

**(The algorithmic typing relation)**

The algorithmic typing relation is the least relation closed under the rules in the figure.

</div>


### Soundness and completeness {#soundness-and-completeness}

<div class="theorem">

**(Soundness)**

If \\(\Gamma \mapsto t : T\\), then \\(\Gamma \vdash t : T\\).

</div>

<div class="proof">

根据 type derivations 进行归纳即可。Algorithmic typing relation 的推导规则和 declarative typing relation 几乎完全相同，唯一的区别在于 `TA-App`，它等价于先用 `T-Sub` 再用 `T-App`。

</div>

<div class="theorem">

**(Completeness / Minimal Typing)**

If \\(\Gamma \vdash t : T\\), then \\(\Gamma \mapsto t : S\\) for some \\(S <: T\\).

</div>

<div class="proof">

根据 declarative type derivations 进行归纳，考虑根据 derivations 中最后一条规则。这里需要注意的是在 algorithmic typing relation 中，推导的结果可能是实际结果的 subtype，即可能会更“小”，因此需要证明这个：

-   `T-Var`：立即由 TA-Var 得出。
-   `T-Abs`：

    \begin{aligned}
    & t = \lambda x:T\_1. t\_2 \\\\
    & \Gamma, x:T\_1 \vdash t\_2 : T\_2 \\\\
    & T = T\_1 \rightarrow T\_2
    \end{aligned}

    根据归纳假设，存在某个 \\(S\_2 <: T\_2\\) 使得 \\(\Gamma, x:T\_1 \mapsto t\_2 : S\_2\\)。由 `TA-Abs` 有，\\(\Gamma \mapsto t : T\_1 \rightarrow S\_2\\)。

    由 `S-Arrow`，\\(T\_1 \rightarrow S\_2 <: T\_1 \rightarrow T\_2\\)，成立。
-   `T-App`：如果 \\(t = t\_1\ t\_2\\)，且 \\(\Gamma \vdash t\_1 : T\_{11} \rightarrow T\_{12}\\) 和 \\(\Gamma \vdash t\_2 : T\_{11}\\)，其中 \\(T = T\_{12}\\)。根据归纳假设，存在某个 \\(S\_1 <: T\_{11} \rightarrow T\_{12}\\) 使得 \\(\Gamma \vdash^n t\_1 : S\_1\\)，且存在某个 \\(S\_2 <: T\_{11}\\) 使得 \\(\Gamma \vdash^n t\_2 : S\_2\\)。根据子类型关系的反演引理（15.3.2），\\(S\_1\\) 必须有形式 \\(S\_{11} \rightarrow S\_{12}\\)，对于某些 \\(S\_{11}\\) 和 \\(S\_{12}\\) 有 \\(T\_{11} <: S\_{11}\\) 且 \\(S\_{12} <: T\_{12}\\)。通过传递性，\\(S\_2 <: S\_{11}\\)。根据算法子类型的完备性（16.2.6 16.3.2），\\(\vdash^n S\_2 <: S\_{11}\\)。现在，由 TA-App，\\(\Gamma \vdash^n t\_1 t\_2 : S\_{12}\\)，完成此情况（因为我们已经有 \\(S\_{12} <: T\_{12}\\)）。
-   `T-Rcd`：如果 \\(t = \\{l\_i=t\_i\ i\in1..n\\}\\)，且 \\(\Gamma \vdash t\_i : T\_i\\) 对每个 \\(i\\)，其中 \\(T = \\{l\_i:T\_i\ i\in1..n\\}\\)。直接得出。
-   `T-Proj`：如果 \\(t = t\_1.l\_j\\)，且 \\(\Gamma \vdash t\_1 : \\{l\_i:T\_i\ i\in1..n\\}\\)，其中 \\(T = T\_j\\)。类似于应用情况。
-   `T-Sub`：如果 \\(t : S\\) 且 \\(S <: T\\)，直接得出。

</div>


## Joins and Meets {#joins-and-meets}

在一个控制流分支中，多个分支可能返回不同的类型。

\\[ \operatorname{if}\ \operatorname{true}\ \operatorname{then}\ \\{x=\operatorname{true},y=\operatorname{false}\\}\ \operatorname{else}\ \\{x=\operatorname{false},z=\operatorname{true}\\} \\]

在没有 subtyping 的时候这个表达式不能通过类型检查，但是在 declarative subtyping 下这个表达式的返回值可以是 \\(\\{x=\operatorname{bool}\\}\\) 或者 \\(\\{\\}\\)，而在 algorithmic subtyping 下应当取这些类型的 minimal type，也就是**最小公共父类型（least common supertype）**。此时称得到的类型是这几个 branches 的 **join**。

<div class="definition">

**(join)**

A type \\(J\\) is called **join** of a pair of types \\(S\\) and \\(T\\), written \\(J = S \vee T\\), if \\(S <: J\\) and \\(T <: J\\), and for all types \\(U\\), if \\(S <: U\\) and \\(T <: U\\), then \\(J <: U\\).

</div>

<div class="definition">

**(meet)**

A type \\(M\\) is called **meet** of a pair of types \\(S\\) and \\(T\\), written \\(M = S \wedge T\\), if \\(M <: S\\) and \\(M <: T\\), and for all types \\(L\\), if \\(L <: S\\) and \\(L <: T\\), then \\(L <: M\\).

</div>

对于一个 subtyping 关系，如果对于每个类型 \\(S\\) 和 \\(T\\) 都有 joins，则这个 subtyping 关系有 joins。类似地，如果对于每个类型 \\(S\\) 和 \\(T\\) 都有 meets，则这个 subtyping 关系有 meets。由于这里讨论的 subtyping 只有 \\(\operatorname{\mathrm{Top}}\\) 而没有 \\(\operatorname{\mathrm{Bot}}\\)，因此只存在 joins 而没有 meets。

Joins 和 meets 的性质有一个弱化版本：如果一对类型 \\(S\\) 和 \\(S\\) 存在某个类型 \\(L\\) 使得 \\(L <: S\\) 且 \\(L <: T\\)，那么这对类型 \\(S\\) 和 \\(T\\) 有**下界（bounded below）**。对于每一对**有下界**的类型 \\(S\\) 和 \\(T\\)，如果存在某个 \\(M\\) 是 \\(S\\) 和 \\(T\\) 的下界，则该 subtyping 关系被认为具有**有界下界（bounded below meets）**。

Joins 和 meets 不是唯一的，例如 \\(\\{x: \operatorname{\mathrm{Top}}, y: \operatorname{\mathrm{Top}}\\}\\) 和 \\(\\{y: \operatorname{\mathrm{Top}}, x: \operatorname{\mathrm{Top}}\\}\\) 可以同时是某个类型的 joins。但是某对类型的 joins 和 meets 假设有多个，那么它们之间一定互为 subtyping 关系。

利用 joins 和 meets 可以定义出 \\(\operatorname{\mathrm{if}}\\) 的 typing rule:

\\[
\dfrac{\Gamma \vdash t\_1 : T\_1 \quad T\_1 = \operatorname{\mathrm{Bool}} \qquad \Gamma \vdash t\_2 : T\_2 \quad \Gamma \vdash t\_3 : T\_3 \quad T\_2 \vee T\_3 = T
        }{\Gamma \vdash \operatorname{if}\ t\_1\ \operatorname{then}\ t\_2\ \operatorname{else}\ t\_3 : T} \tag{TA-If}
\\]

但是 joins 和 meets 也有可能让类型推导变得更奇怪：例如表达式 \\(\operatorname{if}\ \operatorname{true}\ \operatorname{then}\ \operatorname{true}\ \operatorname{else}\ \\{\\}\\) 的类型为 \\(\operatorname{\mathrm{Top}}\\)，这通常不是程序员想要的。通常情况下应当排除掉 joins 为 \\(\operatorname{\mathrm{Top}}\\) 的情况或者直接发出警告。


### Existence of joins and bounded meets {#existence-of-joins-and-bounded-meets}

<div class="proposition">

**(Existence of joins and bounded meets)**

1.  For every pair of types \\(S\\) and \\(T\\), there is some type \\(J\\) such that \\(S \vee T = J\\).
2.  For every pair of types \\(S\\) and \\(T\\) with a common subtype, there is some type \\(M\\) such that \\(S \wedge T = M\\).

</div>

首先给出下面的计算 joins 和 meets 的算法：

\\[
S \vee T = \begin{cases}
\operatorname{\mathrm{Bool}} & \text{if $S = T = \operatorname{\mathrm{Bool}}$} \\\\
M\_1 \to J\_2 & \text{if $S = S\_1 \to S\_2$ and $T = T\_1 \to T\_2$} \\\\
& \quad \text{where $S\_1 \land T\_1 = M\_1$ and $S\_2 \lor T\_2 = J\_2$} \\\\
\\{j\_l : J\_l^{l \in 1 \dots q} \\} & \text{if $S = \\{k\_j : S\_j^{j \in 1 \dots m}\\}$ and $T = \\{l\_i : T\_i^{i \in 1 \dots n}\\}$} \\\\
& \quad \text{where $\\{j\_l^{l \in 1 \dots q}\\} = \\{k\_j^{j \in 1 \dots m}\\} \cap \\{l\_i \\}\_{i \in 1 \dots n}$} \\\\
& \quad \text{and $S\_j \lor T\_i = J\_l$ for each $j = k\_j = l\_i$} \\\\
\operatorname{\mathrm{Top}} & \text{otherwise}
\end{cases}
\\]

\\[
S \wedge T = \begin{cases}
    S & \text{if $T = \operatorname{\mathrm{Top}}$} \\\\
    T & \text{if $S = \operatorname{\mathrm{Top}}$} \\\\
    \operatorname{\mathrm{Bool}} & \text{if $S = T = \operatorname{\mathrm{Bool}}$} \\\\
    J\_1 \to M\_2 & \text{if $S = S\_1 \to S\_2$ and $T = T\_1 \to T\_2$} \\\\
    & \quad \text{where $S\_1 \lor T\_1 = J\_1$ and $S\_2 \land T\_2 = M\_2$} \\\\
    \\{ m\_l : M\_l \\}\_{l \in 1..q} & \text{if $S = \\{ k\_j : S\_j \\}\_{j \in 1..m}$ and $T = \\{ l\_i : T\_i \\}\_{i \in 1..n}$} \\\\
    & \quad \text{where $\\{ m\_l \\}\_{l \in 1..q} = \\{ k\_j \\}\_{j \in 1..m} \cup \\{ l\_i \\}\_{i \in 1..n}$} \\\\
    & \quad \text{and $S\_j \land T\_i = M\_l$ for each $m\_l = k\_j = l\_i$} \\\\
    & \quad \text{and $M\_l = S\_j$ if $m\_l = k\_j$ occurs only in $S$} \\\\
    & \quad \text{and $M\_l = T\_i$ if $m\_l = l\_i$ occurs only in $T$} \\\\
    \operatorname{\mathrm{fail}} & \text{otherwise}
\end{cases}
\\]

这两个算法会相互递归调用（例如计算 \\(S \vee T\\) 的第二个分支上，即函数类型上时，需要计算 \\(S \wedge T\\)）。此处计算 \\(S \wedge T\\) 可能会出现 `fail` 的情况，表明两个类型没有 meets。此时会直接跳到 \\(\operatorname{\mathrm{Top}}\\) 的情况。

在上面的算法中每一个步骤 \\(S\\) 和 \\(T\\) 的 size 都会减小，所以算法一定能够终止，因此 \\(\vee\\) 和 \\(\wedge\\) 都是 total functions。

因此 joins 一定存在，但是 meets 可能会有 `fail` 的情况，下面需要证明如果两个类型有下界，则它们一定有 meets。

<div class="lemma">

If \\(L <: S\\) and \\(L <: T\\), then \\(S \wedge T = M\\) for some \\(M\\).

</div>

<div class="proof">

首先根据 inversion lemma，如果存在 \\(L\\) 满足条件，那么 \\(S\\) 和 \\(T\\) 的形状必定相同。下面根据 size 进行归纳：

-   如果 \\(S = \operatorname{\mathrm{Top}}\\) 或 \\(T = \operatorname{\mathrm{Top}}\\)，那么 \\(S \wedge T\\) 的结果一定是 \\(T\\) 或 \\(S\\)
-   如果 \\(S = \operatorname{\mathrm{Bool}}\\) 且 \\(T = \operatorname{\mathrm{Bool}}\\)，那么 \\(S \wedge T = \operatorname{\mathrm{Bool}}\\)
-   如果 \\(S = S\_1 \to S\_2\\) 且 \\(T = T\_1 \to T\_2\\)。由于 \\(\vee\\) 是 total 的，那么必定存在 \\(J₁\\) 使得 \\(S\_1 \vee T\_1 = J\_1\\)。根据 inversion lemma，\\(L\\) 的形式必定为 \\(L₁ \rightarrow L₂\\)，并且 \\(L₂ <: S₂\\) 和 \\(L₂ <: T₂\\)。根据归纳假设，\\(S₂ \wedge T₂\\) 不会 `fail`，设 \\(S₂ \wedge T₂ = M₂\\)。那么 \\(S \wedge T = J₁ \to M₂\\)
-   如果 \\(S = \\{k\_j : S\_j^{j \in 1 \dots m}\\}\\) 且 \\(T = \\{l\_i : T\_i^{i \in 1 \dots n}\\}\\)。根据 inversion lemma，\\(L\\) 必须是一个 record，其标签包括在 S 和 T 中出现的所有标签；对于 S 和 T 中的每个公共标签，根据 inversion lemma \\(L\\) 中的相应字段是 \\(S\\) 和 \\(T\\) 中字段的共同子类型

</div>

这个 lemma 表明如果两个类型有下界，则它们一定有 meets。

下面证明上面的算法确实计算出了 joins 和 meets：

<div class="proposition">

1.  If \\(S \vee T = J\\), then \\(S <: J\\) and \\(T <: J\\).
2.  If \\(S \wedge T = M\\), then \\(M <: S\\) and \\(M <: T\\).

</div>

<div class="proof">

直接根据算法递归的层次（即调用 \\(\vee\\) 和 \\(\wedge\\) 的次数）进行归纳即可。

</div>


### References {#references}

由于 references 是不变的，因此对于 \\(S = \operatorname{\mathrm{Ref}}(S₁)\\) 和 \\(T = \operatorname{\mathrm{Ref}}(T₁)\\) 有 \\(S \vee T = \operatorname{\mathrm{Ref}}(S₁)\ \operatorname{\mathrm{or}}\ \operatorname{\mathrm{Ref}}(T₁)\\) 当且仅当 \\(S₁ <: T₁\\) 且 \\(T₁ <: S₁\\)。同理，\\(S \wedge T = \operatorname{\mathrm{Ref}}(S₁)\ \operatorname{\mathrm{and}}\ \operatorname{\mathrm{Ref}}(T₁)\\) 当且仅当 \\(S₁ <: T₁\\) 且 \\(T₁ <: S₁\\)。

但是如果通过 `Source` 和 `Sink` 来表示 references，那么这个 subtyping 关系中将不会存在 joins 和 meets。例如类型 \\(\operatorname{\mathrm{Ref}}\\{a:\operatorname{\mathrm{Nat}},b:\operatorname{\mathrm{Bool}}\\}\\) 和 \\(\operatorname{\mathrm{Ref}}\\{a:\operatorname{\mathrm{Nat}}\\}\\) 都是 \\(\operatorname{\mathrm{Source}}\\{a:\operatorname{\mathrm{Nat}}\\}\\) 和 \\(\operatorname{\mathrm{Sink}}\\{a:\operatorname{\mathrm{Nat}},b:\operatorname{\mathrm{Bool}}\\}\\) 的子类型，但是它们没有共同的下界。

对于这个问题的一个解决方案是在类型系统中只加入 `Source` 或 `Sink` 二者之一。假设只加入 `Source`，那么有：

\\[
S \vee T = \begin{cases}
& \dots && \\\\
& \operatorname{\mathrm{Source}}(J) && \text{if $S = \operatorname{\mathrm{Ref}}(S\_1)$, $T = \operatorname{\mathrm{Ref}}(T\_1)$, $J = S\_1 \vee T\_1$} \\\\
& \operatorname{\mathrm{Source}}(J) && \text{if $S = \operatorname{\mathrm{Source}}(S\_1)$, $T = \operatorname{\mathrm{Ref}}(T\_1)$, $J = S\_1 \vee T\_1$} \\\\
& \operatorname{\mathrm{Source}}(S\_1) && \text{if $S = \operatorname{\mathrm{Ref}}(S\_1)$, $T = \operatorname{\mathrm{Source}}(T\_1)$, $J = S\_1 \vee T\_1$} \\\\
& \operatorname{\mathrm{Source}}(S\_1) && \text{if $S = \operatorname{\mathrm{Source}}(S\_1)$, $T = \operatorname{\mathrm{Source}}(T\_1)$, $J = S\_1 \vee T\_1$} \\\\
& \dots
\end{cases}
\\]

另一种解决方案是细化 `Ref`，使其接受两个参数：\\(\operatorname{\mathrm{Ref}}(S, T)\\) **存储**类型 \\(S\\) 并**读取**类型 \\(T\\)。新的 `Ref` 在其第一个参数上是逆变的，在其第二个参数上是协变的。此时 \\(\operatorname{\mathrm{Sink}}\ S \overset{\text{def}}{=} \operatorname{\mathrm{Ref}}\ S\ \operatorname{\mathrm{Top}}\\) ，而 \\(\operatorname{\mathrm{Source}}\ T \overset{\text{def}}{=} \operatorname{\mathrm{Ref}}\ \operatorname{\mathrm{Bot}}\ T\\)。


## Add `Bot` {#add-bot}

如果加入 minimal type \\(\operatorname{\mathrm{Bot}}\\)，需要对上面的规则进行扩展：

\\[\mapsto \operatorname{\mathrm{Bot}} <: T \tag{SA-Bot}\\]

\\[\dfrac{\Gamma \vdash t\_1 : \operatorname{\mathrm{Bot}} \qquad \Gamma \vdash t\_2 : T\_2}{\Gamma \vdash t\_1\ t\_2 : \operatorname{\mathrm{Bot}}} \tag{TA-AppBot}\\]

\\[\dfrac{\Gamma \vdash t\_1 : \operatorname{\mathrm{Bot}}}{\Gamma \vdash t\_1.l\_i : \operatorname{\mathrm{Bot}}} \tag{TA-ProjBot}\\]

考虑 `Bot` 出现在 `if` 的条件中的情况，那么需要加入规则：

\\[\dfrac{\Gamma \vdash t\_1 : \operatorname{\mathrm{Bot}} \qquad \Gamma \vdash t\_2 : T\_2 \qquad \Gamma \vdash t\_3 : T\_3}{\Gamma \vdash \operatorname{if}\ t\_1\ \operatorname{then}\ t\_2\ \operatorname{else}\ t\_3 : T} \tag{TA-IfBot}\\]

注意这里不应该让表达式返回 \\(\operatorname{\mathrm{Bot}}\\)，
