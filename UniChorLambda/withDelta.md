---
title: "UniChorλ"
author: Mako Bates
date: 2023-12-04
subtitle: "choreographic lambda calculus with plurally-located values"
header-includes:
  - \usepackage{amsmath}
  - \usepackage{semantic}
---
\newcommand{\BNF}{\quad\operatorname{::=}\quad}
\newcommand{\BNFOR}{\quad\operatorname{\big{|}}\quad}
\newcommand{\DEF}{{\quad\operatorname{\triangleq}\quad}}
\renewcommand{\rule}[3]{\mathsf{#1} \dubl \frac{\parbox{12cm}{\vspace{0.7em}\centering #2}}{\parbox{12cm}{\centering #3\vspace{0.7em}}}}


\newcommand{\langword}[1]{\operatorname{\mathsf{#1}}}
\newcommand{\INL}{\langword{Inl}}
\newcommand{\INR}{\langword{Inr}}
\newcommand{\CASE}[5]{\langword{case}#1\langword{of}\INL #2 ⇒ #3 ; \INR #4 ⇒ #5}
\newcommand{\DOT}{\langword{.}}
\newcommand{\FST}{\langword{fst}}
\newcommand{\SND}{\langword{snd}}
\newcommand{\PAIR}{\langword{Pair}}
\newcommand{\COMM}[1]{\langword{com}_{#1}}
\newcommand{\nonempty}[1]{#1^{+}}
\newcommand{\id}{\operatorname{\mathit{id}}}

\newcommand{\owners}{\mathtt{owners}}
\newcommand{\roles}{\mathtt{roles}}
### Syntax

\begin{align*}
M  \BNF   &  V                                 \\
   \BNFOR &  M M                               \\
   \BNFOR &  \CASE{M}{x}{M}{x}{M}              \\
                                            \\
V  \BNF   &  x                                 \\
   \BNFOR &  λ x:T \DOT M                      \\
   \BNFOR &  δ x:T \DOT M                      \\
   \BNFOR &  \INL V                             \\
   \BNFOR &  \INR V                             \\
   \BNFOR &  \FST                               \\
   \BNFOR &  \SND                               \\
   \BNFOR &  \PAIR V V                          \\
   \BNFOR &  ()                                \\
   \BNFOR &  \COMM{p;\nonempty{p}}                 \\
                                            \\
d  \BNF   &  ()                                 \\
   \BNFOR &  d + d                              \\
   \BNFOR &  d × d                              \\
                                            \\
t  \BNF   &  d                                   \\
   \BNFOR &  T ↬ T                               \\
   \BNFOR &  T → T                            \\
   \\
T  \BNF   &  t@\nonempty{p}                       \\
   \BNFOR &  T × T                             \\
\end{align*}



I think it's going to be important that the lists of parties at which a value resides
are _lists_, not sets.
That said, it's going to be much easier to write everything if I just casually
use set operators
like union and intersection, and define what they mean in an appendix or something.
Note the use of a super-script "+" to denote vectors instead of a hat or any such.
This is because it's important that these lists never be empty.



### Typing

Partial functions $τ$ map parties to parties,
and naturally extend to mapping types to types.
An explicit $τ$ can be given as a list (set?) of pairs of party names.
TODO: Show explicitly how applying a partial function $τ$ to a type $T$ works,
how it can reduce the owner-pool of data in $T$,
and how it can fail if an owner-pool is reduced to $\emptyset$.
**Failure/undefined $τ(T)$ is grounds for the preconditions of the below rules to fail.**
I use shorthand $\id_{\nonempty{p}}$ to refer to the $τ$ mapping each element of $\nonempty{p}$
to itself and including no other mappings.

\begin{gather*}
\inference[Tlambda]
          {Θ;Γ,(x:T) ⊢ M : T'}
          {Θ;Γ ⊢ (λ x:T \DOT M) : (T → T')@Θ}
          \\
\inference[Tdelta]
          {\roles(T);(x:T) ⊢ M : T'}
          {Θ;Γ ⊢ (δ x:T \DOT M) : (T ↬ T')@Θ}
          \\
\inference[Tvar]
          {x : T \in Γ \quad T' = \id_Θ(T)}
          {Θ;Γ ⊢ x : T' }
          \\
\inference[TappL]
          {Θ;Γ ⊢ M : (T → T')@\nonempty{p}  \quad  /TODO: pick up here.
           \nonempty{p};Γ ⊢ N : T_0  \quad
           \exists τ \mid τ(T)=T_0  \text{  TODO: unique/minimal tau?}}
          {Θ;Γ ⊢ M N : τ(T')}
          \\
\inference[Tcase]
          {Θ;Γ ⊢ N : (d_l + d_r)@\nonempty{p} \quad
           \nonempty{p};Γ,(x_l:d_l@\nonempty{p}) ⊢ M_l : T \quad
           \nonempty{p};Γ,(x_r:d_r@\nonempty{p}) ⊢ M_r : T}
          {Θ;Γ ⊢ \CASE{N}{x_l}{M_l}{x_r}{M_r} : T}
          \\
\inference[Dunit]
          {}
          {Θ;Γ ⊢ () : ()@Θ}
          \\
\inference[Dcom]
          {\text{TODO: this is ugly; the argument will need to be cast down to the single sender.}}
          {Θ;Γ ⊢ \COMM{s;\nonempty{r}} : (d@s → d@\nonempty{r})@Θ}
          \\
\inference[Dpair]
          {Θ;Γ ⊢ V_1 : d_1@\nonempty{p_1} \quad Θ;Γ ⊢ V_2 : d_2@\nonempty{p_2}
           \quad \nonempty{p_1} = \nonempty{p_2}}
          {Θ;Γ ⊢ \PAIR V_1 V_2 : (d_1 × d_2)@\nonempty{p_1}}
          \\
\inference[Tpair]
          {Θ;Γ ⊢ V_1 : T_1 \quad Θ;Γ ⊢ V_2 : T_2}
          {Θ;Γ ⊢ \PAIR V_1 V_2 : T_1 × T_2}
          \\
\inference[Tproj1]
          {}
          {Θ;Γ ⊢ \FST : ((T_1 × T_2) → T_1)@Θ}
\inference[Dproj1]
          {}
          {Θ;Γ ⊢ \FST : ((d_1 × d_2)@\nonempty{p} → d_1@\nonempty{p})@Θ}
          \\
\inference[Tproj2]{\dots}{\dots}
\inference[Dproj2]{\dots}{\dots}
\\
\inference[Dinl]
          {Θ;Γ ⊢ V : d@\nonempty{p}}
          {Θ;Γ ⊢ \INL V : (d + d')@\nonempty{p}}
\inference[Dinr]{\dots}{\dots}
          \\
\end{gather*}



#### Interesting rules

- $\COMM{s;\nonempty{r}}$ : I really think we should make sure we can't send functions.
  Probably I need to restructure the type system somehow
  so that the new location can be clearly defined.
  The substitution of roles during send in Chorλ is actually
  a little more nuanced than I thought.



