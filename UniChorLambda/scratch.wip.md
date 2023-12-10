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
\newcommand{\myference}[3]{\inference[\textsc{#1}]{#2}{#3}}

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
And maybe sets would be fine; IDK.
Note the use of a super-script "+" to denote vectors instead of a hat or any such.
This is because it's important that these lists never be empty.



### Typing

\begin{align*}
\owners(T_1, \dots, T_n) \DEF & ⋃_{i=1}^n \owners(T_i)
\vdbl
\owners(t@\nonempty{p}) \DEF & \nonempty{p} \\
\end{align*}

> **Theorem "Owners":**  
> If $Θ;Γ ⊢ M : T$, then $\owners(T) \subseteq Θ$.  
> PROOF: TODO.

> **Theorem "Participants":**  
> If $Θ;Γ ⊢ M : (T \to_{Θ'} T')@\nonempty{p}$,  
> then $(\owners(T) ∪ \owners(T')) \subseteq Θ' \subseteq @\nonempty{p}$.  
> PROOF: TODO.

Although I'm not here implementing any _location polymorphism_,
I am implementing a form of _subtyping_ based on the location sets.
For best intuitiveness, I write $T ⊑ T'$ to mean $T$ is available to fewer parties than $T'$.
That means values of type $T'$ can be substituted harmlessly for values of type $T$,
which is backward from the usual orientation of subtyping.

\begin{gather*}
\myference{}
          {d ≡ d'}
          {d ⊑ d'}
\end{gather*}

\begin{gather*}
\myference{Tlambda}
          {Θ';Γ,(x:T) ⊢ M : T' \quad \owners(T) \subseteq Θ' \subseteq Θ}
          {Θ;Γ ⊢ (λ x:T \DOT M) : (T →_{Θ'} T')@Θ}
          \vdbl
\myference{Tvar}
          {x : T \in Γ \quad T' = \id_Θ(T)}
          {Θ;Γ ⊢ x : T' }
          \vdbl
\myference{Tapp}
          {Θ;Γ ⊢ M : (T →_{Θ'} T')@\nonempty{p} \quad
           Θ;Γ ⊢ N : T}
          {Θ;Γ ⊢ M N : T'}
          \vdbl
\myference{Tcase}
          {Θ;Γ ⊢ N : (d_l + d_r)@\nonempty{p} \quad
           \nonempty{p};Γ,(x_l:d_l@\nonempty{p}) ⊢ M_l : T \quad
           \nonempty{p};Γ,(x_r:d_r@\nonempty{p}) ⊢ M_r : T}
          {Θ;Γ ⊢ \CASE{N}{x_l}{M_l}{x_r}{M_r} : T}
          \vdbl
\myference{Tunit}
          {}
          {Θ;Γ ⊢ () : ()@Θ}
          \vdbl
\myference{Tcom}
          {\nonempty{r} \subseteq Θ}
          {Θ;Γ ⊢ \COMM{\nonempty{r}} : (d@s → d@\nonempty{r})@Θ}
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
          {}
          {Θ;Γ ⊢ \FST : ((d_1 × d_2)@\nonempty{p} → d_1@\nonempty{p})@Θ}
          \quad
\myference{Tproj2}{\dots}{\dots}
          \vdbl
\myference{TprojN}
          {}
          {Θ;Γ ⊢ \LOOKUP_i : ((T_1, \dots, T_i, \dots, T_n) → T_i)@Θ}
          \vdbl
\myference{Tinl}
          {Θ;Γ ⊢ V : d@\nonempty{p}}
          {Θ;Γ ⊢ \INL V : (d + d')@\nonempty{p}}
          \quad
\myference{Tinr}{\dots}{\dots}
          \vdbl
\myference{Ttyped}
          {Θ;Γ ⊢ M : T' \quad T = \id_{owners(T)}(T')}
          {Θ;Γ ⊢ (M : T) : T}
\end{gather*}




### Centralized semantics

I think we don't actually need the out-of-order business chor-lambda does,
and it's even less likely that we need to be able to evaluate inside lambdas as they do.
If I'm right about that, then we can ignore all the step-annotations...

In other words, I think the central semantics should deviate from normal lambda-calculus
as little as possible, if at all.
And then we'll see if we can still prove deadlock freedom.

\begin{gather*}
\myference{AppAbs}
          {}
          {(λ x:T \DOT M) V \step M[x := V]}
          \vdbl
\myference{App1}
          {N \step N'}
          {(λ x:T \DOT M) N \step (λ x:T \DOT M) N'}
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
          {}
          {\CASE{\INL V}{x_l}{M_l}{x_r}{M_r} \step M_l[x_l := V]}
          \quad
\myference{CaseR}
          {\dots}
          {\dots}
          \vdbl
\myference{Proj1}
          {}
          {\FST (\PAIR V_1 V_2) \step V_1}
          \quad
\myference{Proj2}
          {\dots}
          {\dots}
          \quad
\myference{ProjN}
          {}
          {\LOOKUP_i (V_1, \dots, V_i, \dots, V_n) \step V_i}
          \vdbl
\myference{Com1}
          {}
          {\COMM{\nonempty{r}} () \step ()}
          \quad
\myference{ComPair}
          {\COMM{\nonempty{r}} V_1 \step V_1 \quad \COMM{\nonempty{r}} V_2 \step V_2}
          {\COMM{\nonempty{r}} (\PAIR V_1 V_2) \step \PAIR V_1 V_2}
          \vdbl
\myference{ComInl}
          {\COMM{\nonempty{r}} V \step V}
          {\COMM{\nonempty{r}} (\INL V) \step \INL V}
          \quad
\myference{ComInr}
          {\dots}
          {\dots}
          \vdbl
\myference{Erasure}
          {}
          {M : T \step M}
\end{gather*}



> **Theorem "Progress":**
> If $Θ;∅ ⊢ M : T$, then either M is of form $V$ (which cannot step)
> or their exists $M'$ s.t. $M \step M'$.

**Proof**: By induction of typing rules.  
There are eleven base cases and three recursive cases.  
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

- \textsc{Ttyped}: $M$ is of form $M' : T$, and steps by \textsc{Erasure}.
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
  - \textsc{TprojN}: $A$ must be a value of type $(T_1,\dots,T_n)$ (with $i ≤ n$),
    and must type by \textsc{Tvec}, so it must have from $(V_1,\dots,V_n)$,
    so $M$ can step by \textsc{ProjN}.
  - \textsc{Tproj1}: $A$ must be a value of type $(d_1×d_2)@\nonempty{p}$,
    and must type by \textsc{Tpair}, so it must have form $\PAIR V_1 V_2$,
    so $M$ can step by \textsc{Proj1}.
  - \textsc{Tproj2}: (same as \textsc{Tproj1})
  - \textsc{Tcom}: $A$ must be a value of type $d@s$.
    This is possible under \textsc{Tunit}, \textsc{Tpair}, \textsc{Tinl}, or \textsc{Tinr},
    which respectively force forms $()$, $\PAIR V_1 V_2$, $\INL V$, and $\INR V$,
    which respectively allow $M$ to reduce by
    \textsc{Com1}, \textsc{ComPair}, \textsc{ComInl}, and \textsc{ComInr}.
  - \textsc{Tlambda}: $M$ can reduce by \textsc{AppAbs}.


> **Lemma "Substitution":**
> If $Θ;(x:T_x),Γ ⊢ M : T$ and $Θ;Γ ⊢ V : T_x$,
> then $Θ;Γ ⊢ M[x := V] : T$.

**Proof**: By induction of typing rules.  
TODO: 14 cases.

> **Lemma "Bystanders":**
> If $Θ;Γ ⊢ M : T$,
> then $Θ∪Θ';Γ ⊢ M : T'$
> and $T = \id_Θ(T')$.

**Proof**: By induction of typing rules.  
TODO: 14 cases.



> **Theorem "Preservation":**
> If $Θ;Γ ⊢ M : T$ and $M \step M'$,
> then $Θ;Γ ⊢ M' : T'$
> and $T = \id_{owners(T)}(T')$.

**Proof**: By induction on typing rules.
The same eleven base cases fail the assumption that $M$ can step,
so we consider the recursive cases:

- \textsc{Ttyped}: $M$ is of form $M' : T$, and steps by \textsc{Erasure} to $M$.
  The structure of \textsc{Ttyped} already tells us that $Θ;Γ ⊢ M' : T'$
  and $T = \id_{owners(T)}(T')$.
- \textsc{Tcase}: $M$ is of form $\CASE{N}{x_l}{M_l}{x_r}{M_r}$.
  There are three ways it might step:
  - \textsc{CaseL}: $N$ is of form $\INL V$ and $M' = M_l[x_l := V]$.
    From \textsc{Tcase} and **Bystanders** we have that $Θ;Γ,(x_l:d_l@\nonempty{p}) ⊢ M_l : T$.
    From \textsc{Tcase} and \textsc{Tinl} we have that $Θ;Γ⊢V:d@\nonempty{p}$.
    Therefore by **Substitution** $Θ;Γ⊢ M_l[x_l := V] : T$.
    (Apply **ID Mask**, QED.)
  - \textsc{CaseR}: Same as \textsc{CaseL}.
  - \textsc{Case}: $N \step N'$, and by induction and \textsc{Tcase},
    ${Θ;Γ⊢ N' : (d_l + d_r)@\nonempty{q}}$
    where $\nonempty{p} = \id_{\nonempty{p}}(\nonempty{q})$.
    TODO: This is the same as $\nonempty{p} \subseteq \nonempty{q}$.
    ...  
    TODO: Finish this. I think the theorem might not actually be airtight.
    What we're really doing here is erasing location information,
    without which we really should have type preservation.
    But we don't have the machienery on hand to do that explicitly, do we?
    And is it even really what we want?
    Might it be better to augment the typing rules with _implicit_ subtyping?
