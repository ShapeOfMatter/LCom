---
title: "UniChorλ"
author: Mako Bates
date: 2023-12-04
subtitle: "choreographic lambda calculus with plurally-located values"
header-includes:
  - \usepackage{amsmath}
  - \usepackage{mathtools}
  - \usepackage{semantic}
---
\newcommand{\BNF}{\quad\operatorname{::=}\quad}
\newcommand{\BNFOR}{\quad\operatorname{\big{|}}\quad}
\newcommand{\DEF}{{\quad\operatorname{\triangleq}\quad}}
\renewcommand{\rule}[3]{\mathsf{#1} \dubl \frac{\parbox{12cm}{\vspace{0.7em}\centering #2}}{\parbox{12cm}{\centering #3\vspace{0.7em}}}}

\DeclarePairedDelimiter\norm{\lVert}{\rVert}

\newcommand{\langword}[1]{\operatorname{\mathsf{#1}}}
\newcommand{\INL}{\langword{Inl}}
\newcommand{\INR}{\langword{Inr}}
\newcommand{\CASE}[5]{\langword{case}#1\langword{of}\INL #2 ⇒ #3 ; \INR #4 ⇒ #5}
\newcommand{\DOT}{\langword{.}}
\newcommand{\FST}{\langword{fst}}
\newcommand{\SND}{\langword{snd}}
\newcommand{\LOOKUP}{\langword{lookup}}
\newcommand{\PAIR}{\langword{Pair}}
\newcommand{\COMM}[1]{\langword{com}_{#1}}
\newcommand{\nonempty}[1]{{#1^{+}}}
\newcommand{\id}{\operatorname{\mathit{id}}}

\newcommand{\owners}{\mathtt{owners}}
\newcommand{\roles}{\mathtt{roles}}

\newcommand{\step}{\operatorname{\longrightarrow}}

### Syntax

\begin{align*}
M  \BNF   &  V                       && \text{values}          \\
   \BNFOR &  M M                     && \text{function application}          \\
   \BNFOR &  \CASE{M}{x}{M}{x}{M}    \quad&& \text{branch on sum cases}          \\
   \BNFOR &  M : T                   && \text{allow explicit typing, which may reduce a type.}\\
                                            \\
V  \BNF   &  x                       && \text{variables}          \\
   \BNFOR &  λ x:T \DOT M            && \text{function literals}          \\
   \BNFOR &  \INL V                  && \text{injection to sum types}           \\
   \BNFOR &  \INR V                  && \text{}           \\
   \BNFOR &  \FST                    && \text{projection of data pairs}           \\
   \BNFOR &  \SND                    && \text{}           \\
   \BNFOR &  \PAIR V V               && \text{construction of data pairs}           \\
   \BNFOR &  (V, \dots, V)           && \text{construction of heterogeneous vectors}           \\
   \BNFOR &  \LOOKUP_n               && \text{projection of vectors}           \\
   \BNFOR &  ()                      && \text{unit}          \\
   \BNFOR &  \COMM{\nonempty{p}}     && \text{send to recipient parties}            \\
                                            \\
d  \BNF   &  ()                      && \text{we could just leave the data types abstract...}           \\
   \BNFOR &  d + d                   && \text{}           \\
   \BNFOR &  d × d                   && \text{}           \\
                                            \\
t  \BNF   &  d                       && \text{data types are base types}            \\
   \BNFOR &  T →_\nonempty{p} T      && \text{so are functions functions}         \\
   \\
T  \BNF   &  t@\nonempty{p}          && \text{a located base type}             \\
   \BNFOR &  (T, \dots, T)           && \text{"vectors", which are really n-length tuples.}  \\
\end{align*}



I think might be important that the lists of parties at which a value resides
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
**Failure/undefined $τ(T)$ is grounds for the preconditions of the below rules to fail.**
I use shorthand $\id_{\nonempty{p}}$ to refer to the $τ$ mapping each element of $\nonempty{p}$
to itself and including no other mappings.

\begin{align*}
τ(p) \DEF & \begin{cases}
             q                & (p,q) \in τ \\
             \text{undefined} & \text{otherwise}
             \end{cases} \\
τ(\nonempty{p}) \DEF & \begin{cases}
                       \left[ τ(p) \mid p \in \nonempty{p} \text{ s.t. } (p,\_) \in τ \right]
                         & \exists p \in \nonempty{p} \text{ s.t. } (p,\_) \in τ\\
                       \text{undefined}    & \text{otherwise}
                       \end{cases} \\
τ(T_1, \dots, T_n) \DEF & (τ(T_1), \dots, τ(Tn))  \\
τ(d@\nonempty{p}) \DEF & d@τ(\nonempty{p}) \\
τ((T \to_Θ T')@\nonempty{p}) \DEF & \begin{cases}
                                    (τ(T) \to_{τ(Θ)} τ(T'))@τ(\nonempty{p})
                                      & \forall p \in Θ: (p,\_) \in τ  \\
                                    \text{undefined}    & \text{otherwise}
                                    \end{cases}
\end{align*}

\begin{align*}
\owners(T_1, \dots, T_n) \DEF & ⋃_{i=1}^n \owners(T_i) \\
\owners(t@\nonempty{p}) \DEF & \nonempty{p} \\
\end{align*}

> **Theorem "Owners":**  
> If $Θ;Γ ⊢ M : T$, then $\owners(T) \subseteq Θ$.  
> PROOF: TODO.

> **Theorem "Participants":**  
> If $Θ;Γ ⊢ M : (T \to_{Θ'} T')@\nonempty{p}$,  
> then $(\owners(T) ∪ \owners(T')) \subseteq Θ' \subseteq @\nonempty{p}$.  
> PROOF: TODO.

\begin{gather*}
\inference[Tlambda]
          {Θ';Γ,(x:T) ⊢ M : T' \quad \owners(T) \subseteq Θ' \subseteq Θ}
          {Θ;Γ ⊢ (λ x:T \DOT M) : (T →_{Θ'} T')@Θ}
          \\
\inference[Tvar]
          {x : T \in Γ \quad T' = \id_Θ(T)}
          {Θ;Γ ⊢ x : T' }
          \\
\inference[Tapp]
          {Θ;Γ ⊢ M : (T →_{Θ'} T')@\nonempty{p} \quad
           Θ;Γ ⊢ N : T}
          {Θ;Γ ⊢ M N : T'}
          \\
\inference[Tcase]
          {Θ;Γ ⊢ N : (d_l + d_r)@\nonempty{p} \quad
           \nonempty{p};Γ,(x_l:d_l@\nonempty{p}) ⊢ M_l : T \quad
           \nonempty{p};Γ,(x_r:d_r@\nonempty{p}) ⊢ M_r : T}
          {Θ;Γ ⊢ \CASE{N}{x_l}{M_l}{x_r}{M_r} : T}
          \\
\inference[Tunit]
          {}
          {Θ;Γ ⊢ () : ()@Θ}
          \\
\inference[Tcom]
          {\nonempty{r} \subseteq Θ}
          {Θ;Γ ⊢ \COMM{\nonempty{r}} : (d@s → d@\nonempty{r})@Θ}
          \\
\inference[Tpair]
          {Θ;Γ ⊢ V_1 : d_1@\nonempty{p_1} \quad
           Θ;Γ ⊢ V_2 : d_2@\nonempty{p_2} \quad
           \nonempty{p_1} ∩ \nonempty{p_2} ≠ ∅}
          {Θ;Γ ⊢ \PAIR V_1 V_2 : (d_1 × d_2)@(\nonempty{p_1} ∩ \nonempty{p_2})}
          \\
\inference[Tvec]
          {Θ;Γ ⊢ V_1 : T_1 \quad \dots \quad Θ;Γ ⊢ V_n : T_n}
          {Θ;Γ ⊢ (V_1, \dots, V_n) : (T_1, \dots T_n)}
          \\
\inference[Tproj1]
          {}
          {Θ;Γ ⊢ \FST : ((d_1 × d_2)@\nonempty{p} → d_1@\nonempty{p})@Θ}
\inference[Tproj2]{\dots}{\dots}
          \\
\inference[TprojN]
          {}
          {Θ;Γ ⊢ \LOOKUP_i : ((T_1, \dots, T_i, \dots, T_n) → T_i)@Θ}
          \\
\inference[Tinl]
          {Θ;Γ ⊢ V : d@\nonempty{p}}
          {Θ;Γ ⊢ \INL V : (d + d')@\nonempty{p}}
\inference[Tinr]{\dots}{\dots}
          \\
\inference[Ttyped]
          {Θ;Γ ⊢ M : T' \quad T = \id_{owners(T)}(T')}
          {Θ;Γ ⊢ (M : T) : T}
          \\
\end{gather*}




### Centralized semantics

I think we don't actually need the out-of-order business chor-lambda does,
and it's even less likely that we need to be able to evaluate inside lambdas as they do.
If I'm right about that, then we can ignore all the step-annotations...

In other words, I think the central semantics should deviate from normal lambda-calculus
as little as possible, if at all.
And then we'll see if we can still prove deadlock freedom.

\begin{gather*}
\inference[AppAbs]
          {}
          {(λ x:T \DOT M) V \step M[x := V]}
          \\
\end{gather*}


