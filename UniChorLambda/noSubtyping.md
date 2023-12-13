---
title: "UniChorλ"
author: Mako Bates
date: 2023-12-04
subtitle: "choreographic lambda calculus with plurally-located values"
header-includes:
  - \usepackage{amsmath}
  - \usepackage{mathtools}
  - \usepackage{semantic}
geometry:
  - margin=1.5cm
---

\newcommand{\vdbl}{\\[8pt]}

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
\newcommand{\FST}[1]{\langword{fst}_{#1}}
\newcommand{\SND}[1]{\langword{snd}_{#1}}
\newcommand{\LOOKUP}[2]{\langword{lookup}^{#1}_{#2}}
\newcommand{\PAIR}{\langword{Pair}}
\newcommand{\COMM}[2]{\langword{com}_{#1;#2}}
\newcommand{\nonempty}[1]{{#1^{+}}}
\newcommand{\id}{\operatorname{\mathit{id}}}

\newcommand{\owners}{\mathtt{owners}}
\newcommand{\roles}{\mathtt{roles}}
\newcommand{\mask}{⊳}
\newcommand{\idempotent}[2]{\mathtt{idempotent}^{\mask #1}\!\!(#2)}

\newcommand{\step}{\operatorname{\longrightarrow}}
\newcommand{\myference}[3]{\inference[\textsc{#1}]{#2}{#3}}

## Syntax

\begin{align*}
M  \BNF   &  V                       && \text{values}          \\
   \BNFOR &  M M                     && \text{function application}          \\
   \BNFOR &  \CASE{M}{x}{M}{x}{M}    \quad&& \text{branch on sum cases}          \\
                                            \\
V  \BNF   &  x                       && \text{variables}          \\
   \BNFOR &  (λ x:T \DOT M)@\nonempty{p}            && \text{function literals annotated with participants}          \\
   \BNFOR &  ()@\nonempty{p}                      && \text{unit at locations}          \\
   \BNFOR &  \INL V                  && \text{injection to sum types}           \\
   \BNFOR &  \INR V                  && \text{}           \\
   \BNFOR &  \PAIR V V               && \text{construction of data pairs}           \\
   \BNFOR &  (V, \dots, V)           && \text{construction of heterogeneous vectors}           \\
   \BNFOR &  \FST{\nonempty{p}}      && \text{projection of data pairs}           \\
   \BNFOR &  \SND{\nonempty{p}}      && \text{}           \\
   \BNFOR &  \LOOKUP{n}{\nonempty{p}}   && \text{projection of vectors}           \\
   \BNFOR &  \COMM{p}{\nonempty{p}}     && \text{send to recipient parties}            \\
                                            \\
d  \BNF   &  ()         && \text{alternately, we could abstract over the data types,}   \\
   \BNFOR &  d + d                   && \text{or omit them and just have Unit,}           \\
   \BNFOR &  d × d                   && \text{or provide a single data type of Naturals.}   \\
                                            \\
t  \BNF   &  d                       && \text{data types are base types}            \\
   \BNFOR &  T → T      && \text{so are functions functions}         \\
   \\
T  \BNF   &  t@\nonempty{p}          && \text{a located base type}             \\
   \BNFOR &  (T, \dots, T)           && \text{"vectors" or n-length tuples.}  \\
\end{align*}



Note the use of a super-script "+" to denote sets/lists of parties instead of a hat or bold;
this is because it's important that these lists never be empty.
The type and semantic rules will enforce this as an invariant.


\pagebreak
## Masking

A masking operator "$\mask$" gets used in the typing rules.
Note that this can fail, in which case the relevant precondition of the typing rule fails.

### Type-masking rules

\begin{gather*}
\myference{MTdata}
          {\nonempty{p} ∩ Θ ≠ ∅}
          {d@\nonempty{p} \mask Θ \DEF d@(\nonempty{p} ∩ Θ)}
          \quad
\myference{MTfunction}
          {\nonempty{p} \subseteq Θ}
          {(T → T')@\nonempty{p} \mask Θ \DEF (T → T')@\nonempty{p}}
          \vdbl
\myference{MTvector}
          {T_1' = T_1 \mask Θ, \quad \dots \quad T_n' = T_n \mask Θ}
          {(T_1, \dots, T_n) \mask Θ \DEF (T_1', \dots, T_n')}
\end{gather*}


To provide exact type preservation, and to not simply erase all location data during evaluation,
we need to extend the masking operator to values.

### Value-masking rules

\begin{gather*}
\myference{MVlambda}
          {\nonempty{p} \subseteq Θ}
          {(λ x:T \DOT M)@\nonempty{p} \mask Θ \DEF (λ x:T \DOT M)@\nonempty{p}}
          \quad
\myference{MVunit}
          {\nonempty{p} ∩ Θ ≠ ∅}
          {()@\nonempty{p} \mask Θ \DEF ()@(\nonempty{p} ∩ Θ)}
          \vdbl
\myference{MVinL}
          {V' = V \mask Θ}
          {\INL V \mask Θ \DEF \INL V'}
          \quad
\myference{MVinR}
          {\dots}
          {\dots}
          \quad
\myference{MVproj1}
          {\nonempty{p} \subseteq Θ}
          {\FST{\nonempty{p}} \mask Θ \DEF \FST{\nonempty{p}}}
          \quad
\myference{MVproj2}
          {\dots}
          {\dots}
          \vdbl
\myference{MVpair}
          {V_1' = V_1 \mask Θ \quad V_2' = V_2 \mask Θ}
          {\PAIR V_1 V_2 \mask Θ \DEF \PAIR V_1' V_2'}
          \quad
\myference{MVvector}
          {V_1' = V_1 \mask Θ \quad \dots \quad V_n' = V_n \mask Θ}
          {(V_1, \dots, V_n) \mask Θ \DEF (V_1', \dots, V_n')}
          \vdbl
\myference{MVprojN}
          {\nonempty{p} \subseteq Θ}
          {\LOOKUP{n}{\nonempty{p}} \mask Θ \DEF \LOOKUP{n}{\nonempty{p}}}
          \quad
\myference{MVcom}
          {(s,\nonempty{r}) \subseteq Θ}
          {\COMM{s}{\nonempty{r}} \mask Θ \DEF \COMM{s}{\nonempty{r}}}
          \quad
\myference{MVvar}
          {}
          {x \mask Θ \DEF x}
\end{gather*}


### Lemma "Sub-Mask"

> If $Θ;Γ ⊢ V : d@\nonempty{p}$ and $∅ ≠ \nonempty{q} \subseteq \nonempty{p}$,
> then **A:** $d@\nonempty{p} \mask \nonempty{q} = d@\nonempty{q}$ is defined
> and **B:** $V \mask \nonempty{q}$ is also defined and types as $d@\nonempty{q}$.

**Proof**: Part A is obvious.
Part B follows by induction on the definition of masking for values.

- Lambda: Base case; can't happen because it wouldn't allow a data type.
- Unit: Base case; passes definition and typing.
- Injection L/R: Recursive cases.
- Pair: Recursive case.
- Vector: Base case, can't happen because it wouldn't allow a data type.
- Fst, Snd, Lookup, and Com: Base cases, can't happen because they wouldn't allow a data type.

TODO: lock down the recursive cases above better?

### Lemma "Maskable"

> If $Θ;Γ ⊢ V : T$ and $T \mask \nonempty{p} = T'$,
> then **A:** $V \mask \nonempty{p} = V'$ is defined
> and **B:** $Θ;Γ ⊢ V' : T'$.

**Proof**:
By induction on the definition of masking for values.

- Lambda: Base case. From the type-masking assumption, $\nonempty{p}$ is a superset of the owners,
  so $T' = T$, so $V' = V$.
- Unit: Base case; passes definition and typing.
- Injection L/R: Recursive cases.
- Pair: Recursive case.
- Vector: Recursive case.
- Fst, Snd, Lookup, and Com:
  From the typing assumption, $\nonempty{p}$ is a superset of the owners,
  so $T' = T$ and $V' = V$.


\pagebreak
## Typing

The typing rules \textsc{Tlambda} and \textsc{TprojN} highlight their particular case of masking
by using $\idempotent{\nonempty{p}}{T}$ to stand for the predicate $T = T \mask \nonempty{p}$.
Possibly these rules are actually too strict, IDK.

\begin{gather*}
\myference{Tlambda}
          {\nonempty{p};Γ,(x:T) ⊢ M : T' \quad
           \nonempty{p} \subseteq Θ \quad
           \idempotent{\nonempty{p}}{T}}
          {Θ;Γ ⊢ (λ x:t \dot m)@\nonempty{p} : (T → T')@\nonempty{p}}
          \vdbl
\myference{Tvar}
          {x : T \in Γ \quad T' = T \mask Θ}
          {Θ;Γ ⊢ x : T' }
          \vdbl
\myference{Tapp}
          {Θ;Γ ⊢ M : (T_a → T_r)@\nonempty{p} \quad
           Θ;Γ ⊢ N : T_a' \quad
           T_a' \mask \nonempty{p} = T_a}
          {Θ;Γ ⊢ M N : T_r}
          \vdbl
\myference{Tcase}
          {Θ;Γ ⊢ N : (d_l + d_r)@\nonempty{p} \quad
           \nonempty{p};Γ,(x_l:d_l@\nonempty{p}) ⊢ M_l : T \quad
           \nonempty{p};Γ,(x_r:d_r@\nonempty{p}) ⊢ M_r : T}
          {Θ;Γ ⊢ \CASE{N}{x_l}{M_l}{x_r}{M_r} : T}
          \vdbl
\myference{Tunit}
          {\nonempty{p} \subseteq Θ}
          {Θ;Γ ⊢ ()@\nonempty{p} : ()@\nonempty{p}}
          \vdbl
\myference{Tcom}
          {s,\nonempty{r} \subseteq Θ}
          {Θ;Γ ⊢ \COMM{s}{\nonempty{r}} : (d@s → d@\nonempty{r})@(s,\nonempty{r})}
          \vdbl
\myference{Tpair}
          {Θ;Γ ⊢ V_1 : d_1@\nonempty{p_1} \quad
           Θ;Γ ⊢ V_2 : d_2@\nonempty{p_2} \quad
           \nonempty{p_1} ∩ \nonempty{p_2} ≠ ∅}
          {Θ;Γ ⊢ \PAIR V_1 V_2 : (d_1 × d_2)@(\nonempty{p_1} ∩ \nonempty{p_2})}
          \vdbl
\myference{Tvec}
          {Θ;Γ ⊢ V_1 : T_1 \quad \dots \quad Θ;Γ ⊢ V_n : T_n}
          {Θ;Γ ⊢ (V_1, \dots, V_n) : (T_1, \dots T_n)}
          \vdbl
\myference{Tproj1}
          {\nonempty{p} \subseteq Θ}
          {Θ;Γ ⊢ \FST{\nonempty{p}} : ((d_1 × d_2)@\nonempty{p} → d_1@\nonempty{p})@\nonempty{p}}
          \quad
\myference{Tproj2}{\dots}{\dots}
          \vdbl
\myference{TprojN}
          {\nonempty{p} \subseteq Θ \quad
           \idempotent{\nonempty{p}}{(T_1, \dots, T_n)}}
          {Θ;Γ ⊢ \LOOKUP{i}{\nonempty{p}} : ((T_1, \dots, T_i, \dots, T_n) → T_i)@\nonempty{p}}
          \vdbl
\myference{Tinl}
          {Θ;Γ ⊢ V : d@\nonempty{p}}
          {Θ;Γ ⊢ \INL V : (d + d')@\nonempty{p}}
          \quad
\myference{Tinr}{\dots}{\dots}
\end{gather*}





\pagebreak
## Centralized semantics

I think we don't actually need the out-of-order business chor-lambda does,
and it's even less likely that we need to be able to evaluate inside lambdas as they do.
If I'm right about that, then we can ignore all the step-annotations...

In other words, I think the central semantics should deviate from normal lambda-calculus
as little as possible, if at all.
And then we'll see if we can still prove deadlock freedom.

\begin{gather*}
\myference{AppAbs}
          {V' = V \mask \nonempty{p}}
          {((λ x:T \DOT M)@\nonempty{p}) V \step M[x := V']}
          \vdbl
\myference{App1}
          {N \step N'}
          {((λ x:T \DOT M)\nonempty{p}) N \step ((λ x:T \DOT M)\nonempty{p}) N'}
          \quad
\myference{App2}
          {M \step M'}
          {M N \step M' N}
          \vdbl
\myference{Case}
          {N \step N'}
          {\CASE{N}{x_l}{M_l}{x_r}{M_r} \step \CASE{N'}{x_l}{M_l}{x_r}{M_r}}
          \vdbl
\myference{CaseL}
          {\text{I don't think we need a $V'$?}}
          {\CASE{\INL V}{x_l}{M_l}{x_r}{M_r} \step M_l[x_l := V]}
          \quad
\myference{CaseR}
          {\dots}
          {\dots}
          \vdbl
\myference{Proj1}
          {V' = V_1 \mask \nonempty{p}}
          {\FST{\nonempty{p}} (\PAIR V_1 V_2) \step V'}
          \quad
\myference{Proj2}
          {\dots}
          {\dots}
          \quad
\myference{ProjN}
          {V' = V_i \mask \nonempty{p}}
          {\LOOKUP{i}{\nonempty{p}} (V_1, \dots, V_i, \dots, V_n) \step V'}
          \vdbl
\myference{Com1}
          {()@\nonempty{p} \mask \{s\} = ()@s}
          {\COMM{s}{\nonempty{r}} ()@\nonempty{p} \step ()@\nonempty{r}}
          \quad
\myference{ComPair}
          {\COMM{s}{\nonempty{r}} V_1 \step V_1' \quad \COMM{s}{\nonempty{r}} V_2 \step V_2'}
          {\COMM{s}{\nonempty{r}} (\PAIR V_1 V_2) \step \PAIR V_1' V_2'}
          \vdbl
\myference{ComInl}
          {\COMM{s}{\nonempty{r}} V \step V'}
          {\COMM{s}{\nonempty{r}} (\INL V) \step \INL V'}
          \quad
\myference{ComInr}
          {\dots}
          {\dots}
\end{gather*}


### Theorem "Progress"

> If $Θ;∅ ⊢ M : T$, then either M is of form $V$ (which cannot step)
> or their exists $M'$ s.t. $M \step M'$.

**Proof**: By induction of typing rules.  
There are eleven base cases and two recursive cases.  
Base cases:

- \textsc{Tlambda}
- \textsc{Tvar} (can't happen, by assumption)
- \textsc{Tunit}
- \textsc{Tcom}
- \textsc{Tpair}
- \textsc{Tvec}
- \textsc{Tproj1}
- \textsc{Tproj2}
- \textsc{TprojN}
- \textsc{Tinl}
- \textsc{Tinr}

Recursive cases:

- \textsc{Tcase}: $M$ is of form $\CASE{N}{x_l}{M_l}{x_r}{M_r}$
  and ${Θ;∅ ⊢ N : (d_l + d_r)@\nonempty{p}}$.
  By induction, either $N$ can step, in which case M can step by \textsc{Case},
  or $N$ is a value.
  The only tying rules that would give an $N$ of form $V$ the required type are
  \textsc{Tvar} (which isn't compatible with the assumed empty $Γ$),
  and \textsc{Tinl} and \textsc{Tinr}, which respectively force $N$ to have the required forms
  for $M$ to step by \textsc{CaseL} or \textsc{CaseR}.
- \textsc{Tapp}: $M$ is of form $F A$, and $F$ is of a function type and $A$ also types
  (both in the same empty $Γ$).
  By induction, either $F$ can step (so $M$ can step by \textsc{App2}),
  or $A$ can step (so $M$ can step by \textsc{App1}),
  or $F$ and $A$ are both values.
  Ignoring the impossible \textsc{Tvar} cases,
  there are five ways an $F$ of form $V$ could type as a function;
  in each case we get to make some assumption about the type of $A$.
  - \textsc{Tproj1}: $A$ must be a value of type $(d_1×d_2)@\nonempty{p}$,
    and must type by \textsc{Tpair}, so it must have form $\PAIR V_1 V_2$
    where $Θ;∅ ⊢ V_1 : d_1@\nonempty{p1}$
    and $Θ;∅ ⊢ V_2 : d_1@\nonempty{p2}$
    and $\nonempty{p} = \nonempty{p_1} ∩ \nonempty{p_2} ≠ ∅$.
    so $M$ must step by \textsc{Proj1}.
    This is possible by Lemma "Sub-Mask".
  - \textsc{Tproj2}: (same as \textsc{Tproj1})
  - \textsc{TprojN}: $A$ must be a value of type $(T_1,\dots,T_n)$ with $i ≤ n$
    and must type by \textsc{Tvec}, so it must have from $(V_1,\dots,V_n)$,
    and (by unpacking one layer of $\mask$) $T_i \mask \nonempty{p} = T_i$.
    $M$ must step by \textsc{ProjN}.
    By Lemma Maskable, it can.
  - \textsc{Tcom}: $A$ must be a value of type $d@s$.
    This is possible under \textsc{Tunit}, \textsc{Tpair}, \textsc{Tinl}, or \textsc{Tinr},
    which respectively force forms $()$, $\PAIR V_1 V_2$, $\INL V$, and $\INR V$,
    which respectively require that $M$ reduce by
    \textsc{Com1}, \textsc{ComPair}, \textsc{ComInl}, and \textsc{ComInr}.
    In the case of $()$, this follows from Lemma Sub-Mask, since $\{s\} \subseteq \{s\}$;
    the other three are recursive.
  - \textsc{Tlambda}: $M$ must reduce by \textsc{AppAbs}.
    By the assumption of \textsc{Tapp} and Lemma Maskable, it can.





### Theorem "Preservation"

> If $Θ;Γ ⊢ M : T$ and $M \step M'$,
> then $Θ;Γ ⊢ M' : T$.

**Proof**: By induction on typing rules.
The same eleven base cases fail the assumption that $M$ can step,
so we consider the recursive cases:

- \textsc{Tcase}: $M$ is of form $\CASE{N}{x_l}{M_l}{x_r}{M_r}$.
  There are three ways it might step:
  - \textsc{CaseL}: $N$ is of form $\INL V$ and $M' = M_l[x_l := V]$.
    **TODO: fix this.**
  - \textsc{CaseR}: Same as \textsc{CaseL}.
  - \textsc{Case}: $N \step N'$, and by induction and \textsc{Tcase},
    ${Θ;Γ⊢ N' : (d_l + d_r)@\nonempty{p}}$,
    so the original typing judgment will still apply.
- \textsc{Tapp}: $M$ is of form $F A$, and $F$ is of a function type and $A$ also types
  (both in the same $Γ$).
  If the step is by \textsc{App2}or \textsc{App1}, then recursion is easy.
  There are eight other ways the step could happen:
  - \textsc{AppAbs}: 
  - \textsc{Proj1}: 
  - \textsc{Proj2}: 
  - \textsc{ProjN}: 
  - \textsc{Com1}: By \textsc{TCom} and \textsc{Unit}.
  - \textsc{ComPair}: Recusion among the \textsc{Com*} cases.
  - \textsc{ComInl}:  Recusion among the \textsc{Com*} cases.
  - \textsc{ComInr}:  Recusion among the \textsc{Com*} cases.
