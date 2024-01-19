---
title: "UniChorλ"
author: Mako Bates
date: 2023-12-04
subtitle: "choreographic lambda calculus with plurally-located values"
header-includes:
  - \usepackage{amsmath}
  - \usepackage{mathtools}
  - \usepackage{semantic}
  - \usepackage{ifthen}
geometry:
  - margin=1.5cm
---

\newcommand{\vdbl}{\\[8pt]}

\newcommand{\BNF}{\quad\operatorname{::=}\quad}
\newcommand{\BNFOR}{\quad\operatorname{\big{|}}\quad}
\newcommand{\DEF}{{\quad\operatorname{\triangleq}\quad}}
\newcommand{\DEFCASE}{\quad\operatorname{\xRightarrow{△}}\quad}

\DeclarePairedDelimiter\norm{\lVert}{\rVert}

\newcommand{\set}[1]{\left\{#1\right\}}

\newcommand{\langword}[1]{\operatorname{\mathsf{#1}}}
\newcommand{\INL}{\langword{Inl}}
\newcommand{\INR}{\langword{Inr}}
\newcommand{\CASE}[6]{\langword{case}_{#1}#2\langword{of}\INL #3 ⇒ #4 ; \INR #5 ⇒ #6}
\newcommand{\DOT}{\langword{.}}
\newcommand{\FST}[1]{\langword{fst}_{#1}}
\newcommand{\SND}[1]{\langword{snd}_{#1}}
\newcommand{\LOOKUP}[2]{\langword{lookup}^{#1}_{#2}}
\newcommand{\PAIR}{\langword{Pair}}
\newcommand{\COMM}[2]{\langword{com}_{#1;#2}}
\newcommand{\nonempty}[1]{{#1^{+}}}
\newcommand{\id}{\operatorname{\mathit{id}}}
\newcommand{\RECV}[1]{\langword{recv}_{#1}}
\newcommand{\SEND}[1]{\langword{send}_{#1}}

\newcommand{\owners}{\mathtt{owners}}
\newcommand{\roles}[1]{\mathtt{roles}(#1)}
\newcommand{\mask}{⊳}
\newcommand{\noop}[2]{\mathtt{noop}^{\mask #1}\!\!(#2)}
\newcommand{\fresh}[1]{\mathtt{fresh}(#1)}

\newcommand{\step}{\operatorname{\longrightarrow}}
\newcommand{\prcstep}[2]{\xlongrightarrow{ ⊕#1 ; ⊖#2 }}
\newcommand{\netstep}[2]{\xlongrightarrow{ #1 \ifthenelse{\equal{#1}{}}{}{:} #2 }}
\newcommand{\myference}[3]{\inference[\textsc{#1}]{#2}{#3}}

## Syntax

\begin{align*}
M  \BNF   &  V                       && \text{values}          \\
   \BNFOR &  M M                     && \text{function application}          \\
   \BNFOR &  \CASE{\nonempty{p}}{M}{x}{M}{x}{M}    \quad&& \text{branch on sum cases}          \\
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

**From here on we will assume that bound variables are unique.**
It'd be nice to drop this assumption.
I've tried to make it somewhat explicit in the typing rules.

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

**Proof**: Part A is obvious by \textsc{MTdata}.
Part B follows by induction on the definition of masking for values.

- \textsc{MVlambda}: Base case; can't happen because it wouldn't allow a data type.
- \textsc{MVunit}: Base case; passes definition and typing.
- \textsc{MVinL}, \textsc{MVinR}: Recursive cases.
- \textsc{MVpair}: Recursive case.
- \textsc{MVvector}: Can't happen because it wouldn't allow a data type.
- \textsc{MVproj1}, \textsc{MVproj2}, \textsc{MVprojN}, and \textsc{MVcom}:
  Base cases, can't happen because they wouldn't allow a data type.
- \textsc{MVvar}: Base case, trivial.

TODO: lock down the recursive cases above better?

### Lemma "Maskable"

> If $Θ;Γ ⊢ V : T$ and $T \mask \nonempty{p} = T'$,
> then **A:** $V \mask \nonempty{p} = V'$ is defined
> and **B:** $Θ;Γ ⊢ V' : T'$.

**Proof**:
By induction on the definition of masking for values.

- \textsc{MVlambda}: Base case. From the type-masking assumption, \textsc{MTfunction},
  $\nonempty{p}$ is a superset of the owners,
  so $T' = T$, so $V' = V$.
- \textsc{MVunit}: Base case; passes definition and typing.
- \textsc{MVinL}, \textsc{MVinR}: Recursive cases.
- \textsc{MVpair}: Recursive case.
- \textsc{MVvector}: Recursive case.
- \textsc{MVproj1}, \textsc{MVproj2}, \textsc{MVprojN}, and \textsc{MVcom}:
  From the typing assumption, $\nonempty{p}$ is a superset of the owners,
  so $T' = T$ and $V' = V$.
- \textsc{MVvar}: Base case, trivial.


### Lemma "Enclave"

> If $Θ;Γ ⊢ V : T$ and $Θ' \subseteq Θ$
> and $T' = T \mask Θ'$ is defined
> then $V' = V \mask Θ'$ is defined,
> and $Θ';Γ ⊢ V' : T'$.

**Proof**:
This is vacuous if $T'$ doesn't exist, so assume it does.
Do induction on the definition of masking for $T$:

- \textsc{MTdata}: $Θ;Γ ⊢ V : d@\nonempty{p}$ and $\nonempty{p} ∩ Θ' ≠ ∅$
  so $T' = d@(\nonempty{p} ∩ Θ')$.
  Consider cases for typing of $V$:
  - \textsc{Tvar}: $V' = V$ by \textsc{MVvar} and it types by \textsc{Tvar} b.c. $T'$ exists.
  - \textsc{Tunit}: We've already assumed the preconditions for \textsc{MVunit}, and it types.
  - \textsc{Tpair}: $V = \PAIR V_1 V_2$,
    and $Θ;Γ ⊢ V_1 : d_1@(\nonempty{p_1} \supseteq \nonempty{p})$
    and $Θ;Γ ⊢ V_2 : d_2@(\nonempty{p_2} \supseteq \nonempty{p})$.
    By \textsc{MTdata}, these larger-owernership types will still mask with $Θ'$,
    so this case come by induction.
  - \textsc{TinL}, \textsc{TinR}: Follows by simple induction.
- \textsc{MTFunction}: $T' = T$ and $\nonempty{p} \subseteq Θ'$,
  so lambdas and function-keywords all project unchanged, and the respective typings hold.
- \textsc{MTVector}: Simple induction.


### Lemma "Quorum"

> **A)** If $Θ;Γ,(x:T_x) ⊢ M : T$ and $T_x' = T_x \mask Θ$, then $Θ;Γ,(x:T_x') ⊢ M : T$.  
> **B)** If $Θ;Γ,(x:T_x) ⊢ M : T$ and $T_x \mask Θ$ is not defined, then $Θ;Γ ⊢ M : T$.

**Proof**: By induction on the typing of M.
The only case that's not recursive or trivial is \textsc{TVar},
for which we just need to observe that masking on a given party-set is idempotent.



\pagebreak
## Typing

The typing rules \textsc{Tlambda} and \textsc{TprojN} highlight their particular case of masking
by using $\noop{\nonempty{p}}{T}$ to stand for the predicate $T = T \mask \nonempty{p}$.
Possibly these rules are actually too strict, IDK.

\begin{gather*}
\myference{Tlambda}
          {\nonempty{p};Γ,(x:T) ⊢ M : T' \quad
           \nonempty{p} \subseteq Θ \quad
           \noop{\nonempty{p}}{T} \quad
           \fresh{x}}
          {Θ;Γ ⊢ (λ x:T \DOT M)@\nonempty{p} : (T → T')@\nonempty{p}}
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
          {Θ;Γ ⊢ N : T_N \quad
           (d_l + d_r)@\nonempty{p} = T_N \mask \nonempty{p} \quad
           \nonempty{p};Γ,(x_l:d_l@\nonempty{p}) ⊢ M_l : T \quad
           \nonempty{p};Γ,(x_r:d_r@\nonempty{p}) ⊢ M_r : T \quad
           \nonempty{p} \subseteq Θ \quad
           \fresh{x_l, x_r}}
          {Θ;Γ ⊢ \CASE{\nonempty{p}}{N}{x_l}{M_l}{x_r}{M_r} : T}
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
           \noop{\nonempty{p}}{(T_1, \dots, T_n)}}
          {Θ;Γ ⊢ \LOOKUP{i}{\nonempty{p}} : ((T_1, \dots, T_i, \dots, T_n) → T_i)@\nonempty{p}}
          \vdbl
\myference{Tinl}
          {Θ;Γ ⊢ V : d@\nonempty{p}}
          {Θ;Γ ⊢ \INL V : (d + d')@\nonempty{p}}
          \quad
\myference{Tinr}{\dots}{\dots}
\end{gather*}




### Lemma "Exclave"

> If $Θ;∅ ⊢ M : T$ and $Θ \subseteq Θ'$
> then $Θ';∅ ⊢ M : T$.

**Proof**:
By induction on the typing of $M$.

- \textsc{Tlambda}: The recursive typing is unaffected,
  and the other tests are fine with a larger set.
- \textsc{Tvar}: Can't apply with an empty type context.
- All other cases are unaffected by the larger party-set.





\pagebreak
## Substitution

In the interest of getting exact type preservation,
I'm defining a more discerning than usual substitution process.
There are non-shadowing cases where substitution is forced to a no-op;
I think the Lemma "Substitution" suffices to show that that's ok.

\begin{align*}
M[x:=V] \DEF \text{by pattern matching on $M$:}& \\
y            \DEFCASE & \begin{cases}
                                        y ≡ x & \DEFCASE  V  \\
                                        y ≢ x & \DEFCASE  y
                                        \end {cases} \\
N_1 N_2     \DEFCASE & N_1[x:=V] N_2[x:=V] \\
(λ y:T \DOT N)@\nonempty{p}  \DEFCASE & \begin{cases}
                                        V \mask \nonempty{p} = V'
                                            & \DEFCASE (λ y:T \DOT N[x:=V'])@\nonempty{p} \\
                                        \text{otherwise} & \DEFCASE M
                                        \end{cases} \\
\CASE{\nonempty{p}}{N}{x_l}{M_l}{x_r}{M_r} \DEFCASE & \begin{cases}
                                        V \mask \nonempty{p} = V'
                                            & \!\!\!\!\!\!\!\!  \DEFCASE \!\!\!\! \CASE{\nonempty{p}}
                                                            {N[x:=V]}{x_l}{M_l[x:=V']}
                                                            {x_r}{M_r[x:=V']} \\
                                        \text{otherwise}
                                            & \!\!\!\!\!\!\!\!  \DEFCASE \!\!\!\! \CASE{\nonempty{p}}
                                                            {N[x:=V]}{x_l}{M_l}{x_r}{M_r})
                                        \end{cases} \\
\INL V_1    \DEFCASE & \INL V_1[x:=V] \\
\INR V_2    \DEFCASE & \INR V_2[x:=V] \\
\PAIR V_1 V_2  \DEFCASE & \PAIR V_1[x:=V] V_2[x:=V] \\
(V_1, \dots, V_n) \DEFCASE & (V_1[x:=V], \dots, V_n[x:=V]) \\
()@\nonempty{p}
          \BNFOR \FST{\nonempty{p}}
          \BNFOR \SND{\nonempty{p}} \qquad\qquad \\
          \BNFOR \LOOKUP{\nonempty{p}}{i}
          \BNFOR \COMM{s}{\nonempty{r}}       \DEFCASE & M
\end{align*}

### Lemma "Unused"

> If $Θ;Γ ⊢ M : T$ and $x \not \in Γ$, then $M[x := V] = M$.

**Proof**:
By induction on the typing of $M$.
There are no non-trivial cases.

### Lemma "Substitution"

> If $Θ;Γ,(x:T_x) ⊢ M : T$ and $Θ;Γ ⊢ V : T_x$,
> then $Θ;Γ ⊢ M[x := V] : T$.

**Proof**: Induction on the typing rules for $M$.
There are 13 cases.
\textsc{TprojN}, \textsc{Tproj1}, \textsc{Tproj2}, \textsc{Tcom}, and \textsc{Tunit}
are trivial base cases.
\textsc{TinL}, \textsc{TinR}, , \textsc{Tvec}, and \textsc{Tpair}
are trivial recursive cases.

- \textsc{Tlambda} where $T_x' = T_x \mask \nonempty{p}$:
  $M = (λ y : T_y \DOT N)@\nonempty{p}$ and $T = (T_y → T')@\nonempty{p}$.
  1. $Θ;Γ,(x:T_x) ⊢ (λ y : T_y \DOT N)@\nonempty{p} : (T_y → T')@\nonempty{p}$ by assumption.
  2. $Θ;Γ ⊢ V : T_x$ by assumption.
  3. $\nonempty{p};Γ,(x:T_x),(y:T_y) ⊢ N : T'$ per preconditions of \textsc{Tlambda}.
  4. $Θ;Γ,(y:T_y) ⊢ V : T_x$ by weakening (or strengthening?) #2.
  5. $V' = V \mask \nonempty{p}$ and $\nonempty{p}; Γ,(y:T_y) ⊢ V' : T_x'$ by Lemma "Enclave".
  6. $\nonempty{p};Γ,(x:T_x'),(y:T_y) ⊢ N : T'$ by applying Lemma "Quorum" to #3.
  7. $\nonempty{p};Γ,(y:T_y) ⊢ N[x:=V'] : T'$ by induction on #6 and #5.
  8. $M[x:=V] = (λ y : T_y \DOT N[x:=V'])@\nonempty{p}$ by \textsc{Slambda},
     which typechecks by #7 and \textsc{Tlambda}. _QED._
- \textsc{Tlambda} where $T_x \mask \nonempty{p}$ is undefined:
  $M = (λ y : T_y \DOT N)@\nonempty{p}$.
  1. $\nonempty{p};Γ,(x:T_x),(y:T_y) ⊢ N : T'$ per preconditions of \textsc{Tlambda}.
  2. $\nonempty{p};Γ,(y:T_y) ⊢ N : T'$ by Lemma "Quorum" B.
  3. $N[x:=V] = N$ by Lemma "Unused",
     so regardless of the existence of $V \mask \nonempty{p}$ the substitution is a noop,
     and it typechecks by #2 and \textsc{Tlambda}.
- \textsc{Tvar}: Follows from the relevant definitions, whether $x ≡ y$ or not.
- \textsc{Tapp}: This is also a simple recursive case;
  the masking of $T_a$ doesn't affect anything.
- \textsc{Tcase}: Follows the same logic as \textsc{Tlambda},
  just duplicated for $M_l$ and $M_r$.




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
          {V' = V \mask \nonempty{p} \quad
           M' = M[x := V']}
          {((λ x:T \DOT M)@\nonempty{p}) V \step M'}
          \vdbl
\myference{App1}
          {N \step N'}
          {V N \step V N'}
          \quad
\myference{App2}
          {M \step M'}
          {M N \step M' N}
          \vdbl
\myference{Case}
          {N \step N'}
          {\CASE{\nonempty{p}}{N}{x_l}{M_l}{x_r}{M_r}
            \step \CASE{\nonempty{p}}{N'}{x_l}{M_l}{x_r}{M_r}}
          \vdbl
\myference{CaseL}
          {V' = V \mask \nonempty{p} \quad
           M_l' = M_l[x_l := V']}
          {\CASE{\nonempty{p}}{\INL V}{x_l}{M_l}{x_r}{M_r} \step M_l'}
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
          {()@\nonempty{p} \mask \set{s} = ()@s}
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

- \textsc{Tcase}: $M$ is of form $\CASE{\nonempty{p}}{N}{x_l}{M_l}{x_r}{M_r}$
  and ${Θ;∅ ⊢ N : (d_l + d_r)@\nonempty{p}}$.
  By induction, either $N$ can step, in which case M can step by \textsc{Case},
  or $N$ is a value.
  The only tying rules that would give an $N$ of form $V$ the required type are
  \textsc{Tvar} (which isn't compatible with the assumed empty $Γ$),
  and \textsc{Tinl} and \textsc{Tinr}, which respectively force $N$ to have the required forms
  for $M$ to step by \textsc{CaseL} or \textsc{CaseR}.
  From the typing rules, \textsc{MTdata}, and the first part of Lemma "Enclave",
  the masking required by the step rules is possible.
- \textsc{Tapp}: $M$ is of form $F A$, and $F$ is of a function type and $A$ also types
  (both in the same empty $Γ$).
  By induction, either $F$ can step (so $M$ can step by \textsc{App2}),
  or $A$ can step (so $M$ can step by \textsc{App1}),
  or $F$ and $A$ are both values.
  Ignoring the impossible \textsc{Tvar} cases,
  there are five ways an $F$ of form $V$ could type as a function;
  in each case we get to make some assumption about the type of $A$.
  Furthermore, by \textsc{Tapp} and Lemma "Enclave",
  we know that $A$ can mask to the owners of $F$.
  - \textsc{Tproj1}: $A$ must be a value of type $(d_1×d_2)@\nonempty{q}$,
    and must type by \textsc{Tpair}, so it must have form $\PAIR V_1 V_2$,
    so $M$ must step by \textsc{Proj1}.
    We know $V_1$ can mask by \textsc{MVpair}.
  - \textsc{Tproj2}: (same as \textsc{Tproj1})
  - \textsc{TprojN}: $A$ must be a value of type $(T_1,\dots,T_n)$ with $i ≤ n$
    and must type by \textsc{Tvec}, so it must have from $(V_1,\dots,V_n)$.
    $M$ must step by \textsc{ProjN}.
    We known $V_i$ can step by \textsc{MVvector}.
  - \textsc{Tcom}: $A$ must be a value of type $d@s$.
    This is possible under \textsc{Tunit}, \textsc{Tpair}, \textsc{Tinl}, or \textsc{Tinr},
    which respectively force forms $()$, $\PAIR V_1 V_2$, $\INL V$, and $\INR V$,
    which respectively require that $M$ reduce by
    \textsc{Com1}, \textsc{ComPair}, \textsc{ComInl}, and \textsc{ComInr}.
    In the case of $()$, this follows from Lemma Sub-Mask,
    since $\set{s} \subseteq \set{s}$;
    the other three are recursive among each other.
  - \textsc{Tlambda}: $M$ must reduce by \textsc{AppAbs}.
    By the assumption of \textsc{Tapp} and Lemma Maskable, it can.





### Theorem "Preservation"

> If $Θ;∅ ⊢ M : T$ and $M \step M'$,
> then $Θ;∅ ⊢ M' : T$.

**Proof**: By induction on typing rules for $M$.
The same eleven base cases fail the assumption that $M$ can step,
so we consider the recursive cases:

- \textsc{Tcase}: $M$ is of form $\CASE{\nonempty{p}}{N}{x_l}{M_l}{x_r}{M_r}$.
  There are three ways it might step:
  - \textsc{CaseL}: $N$ is of form $\INL V$, $V'$ exists, and $M' = M_l[x_l := V']$.
    1. $\nonempty{p};(x_l:d_l@\nonempty{p}) ⊢ M_l : T$ by the preconditions of \textsc{Tcase}.
    2. $Θ;∅ ⊢ V : d_l@\nonempty{p}$ because $N$ must type by \textsc{TinL}.
    3. $\nonempty{p};∅ ⊢ V' : d_l@\nonempty{p}$ by Lemma "Enclave" and \textsc{MTdata}.
       (Do I need to add a $\nonempty{p} \subseteq Θ$ to \textsc{Tcase}?)
    4. $\nonempty{p};∅ ⊢ M_l[x_l := V'] : T$ by Lemma "Substitution".
    5. $Θ;∅ ⊢ M_l[x_l := V'] : T$ by Lemma "Exclave". _QED._
  - \textsc{CaseR}: Same as \textsc{CaseL}.
  - \textsc{Case}: $N \step N'$, and by induction and \textsc{Tcase},
    $Θ;Γ⊢ N' : T_N$,
    so the original typing judgment will still apply.
- \textsc{Tapp}: $M$ is of form $F A$, and $F$ is of a function type and $A$ also types
  (both in the empty typing context).
  If the step is by \textsc{App2}or \textsc{App1}, then recursion is easy.
  There are eight other ways the step could happen:
  - \textsc{AppAbs}: $F$ must type by \textsc{Tlambda}.
    $M = ((λ x : T_x \DOT B)@\nonempty{p}) A$.
    We need to show that $A' = A \mask \nonempty{p}$ exists and $Θ;∅ ⊢ B[x := A'] : T$.
    1. $\nonempty{p};(x:T_x) ⊢ B : T$ by the preconditions of \textsc{Tlambda}.
    2. $Θ;∅ ⊢ A : T_a'$ such that $T_x = T_a' \mask \nonempty{p}$,
       by the preconditions of \textsc{Tapp}.
    4. $A'$ exists and $\nonempty{p};∅ ⊢ A' : T_x$ by Lemma "Enclave" on #2.
    5. $\nonempty{p};∅ ⊢ B[x := A'] : T$ by Lemma "Substitution".
    6. _QED._ by Lemma "Exclave".
  - \textsc{Proj1}: $F = \FST{\nonempty{p}}$ and $A = \PAIR V_1 V_2$ and
    $M' = V_1 \mask \nonempty{p}$.
    Necessarily, by \textsc{Tpair} $Θ;∅ ⊢ V_1 : d_1@\nonempty{p_1}$
    where $\nonempty{p} \subseteq \nonempty{p_1}$.
    By Lemma "Sub-mask", $Θ;∅ ⊢ M' : T$.
  - \textsc{Proj2}: same as \textsc{Proj1}.
  - \textsc{ProjN}: $F = \LOOKUP{i}{\nonempty{p}}$ and $A = (\dots, V_i, \dots)
    and $M' = V_i \mask \nonempty{p}$.
    Necessarily, by \textsc{TVec} $Θ;∅ ⊢ V_i : T_i$ and $Θ;∅ ⊢ A : (\dots, T_i, \dots)$.
    By \textsc{Tapp}, $(\dots, T_i, \dots) \mask \nonempty{p} = T_a$,
    so by \textsc{MTvector} $T_i \mask \nonempty{p}$ exists
    and (again by \textsc{Tapp} and \textsc{TprojN}) it must equal $T$.
    _QED._ by Lemma "Maskable".
  - \textsc{Com1}: By \textsc{TCom} and \textsc{Unit}.
  - \textsc{ComPair}: Recusion among the \textsc{Com*} cases.
  - \textsc{ComInl}:  Recusion among the \textsc{Com*} cases.
  - \textsc{ComInr}:  Recusion among the \textsc{Com*} cases.



\pagebreak
## Process Language

I'll follow Chor-$λ$ as close as I can;
some modification will be necessary beyond just not using everything.

\begin{align*}
B \BNF   & L
             && \text{Process expressions are distinguished as $B$ instead of $M$.} \\
  \BNFOR & B B                && \text{}  \\
  \BNFOR & \CASE{}{B}{x}{B}{x}{B} && \text{} \\
L \BNF   & x \BNFOR ()
             && \text{Process values are distinguished as $L$ instead of $V$.} \\
  \BNFOR & λ x \DOT B     && \text{} \\
  \BNFOR & \INL L \BNFOR \INR L  \\
  \BNFOR & \PAIR L L  \BNFOR  \FST{} \BNFOR \SND{} \\
  \BNFOR & (L, \dots, L) \BNFOR \LOOKUP{n}{} && \text{} \\
  \BNFOR & \RECV{p} \BNFOR \SEND{\nonempty{p}} \BNFOR \SEND{\nonempty{p}}^\ast
             && \text{receive from one party, send to many,
                      send to many \textit{and} keep for oneself} \\
  \BNFOR & ⊥                  && \text{"missing" (someplace else)} \\
\end{align*}

We have an equivalence class on Process Values based on glomming of $⊥$:
$L_1 ≈ L_2$.
This lifts to expressions (_e.g._ $(\INL ⊥) N ≈ ⊥ N$)
and from there to networks
(_e.g._ $p[(\INL ⊥) N] \mid \mathcal{N} ≈ p[⊥] \mid \mathcal{N}$).

\begin{gather*}
\myference{EBpair}
          {}
          {\PAIR ⊥ ⊥ ≈ ⊥}
          \quad
\myference{EBvec}
          {\text{They're \textit{all} $⊥$.}}
          {(⊥, \dots) ≈ ⊥}
          \quad
\myference{EBinl}
          {}
          {\INL ⊥ ≈ ⊥}
          \quad
\myference{EBinr}
          {\dots}
          {\dots}
          \vdbl
\myference{EBpairR1}
          {V_1 ≈ V_1'}
          {\PAIR V_1 V_2 ≈ \PAIR V_1' V_2}
          \quad
\myference{EBpairR2}
          {V_2 ≈ V_2'}
          {\dots}
          \quad
\myference{EBvecR}
          {V ≈ V'}
          {(\dots, V, \dots) ≈ (\dots, V', \dots)}
          \vdbl
\myference{EBinlR}
          {V ≈ V'}
          {\INL V ≈ \INL V'}
          \quad
\myference{EBinrR}
          {\dots}
          {\dots}
\end{gather*}

The process language is untyped; hopefully I don't need it!
Semantic steps are labeled with send ($⊕$) and receive ($⊖$) sets, like so:
$B \prcstep{\set{(p,L_1), (q,L_2)}}{\set{(r, L_3), (s, L_4)}} B'$,
or $B \prcstep{μ}{η} B'$ for short.

\begin{gather*}
\myference{NabsApp}
          {}
          {(λ x \DOT B) L \prcstep{∅}{∅} B[x:=L]}
          \quad
\myference{Napp1}
          {B \prcstep{μ}{η} B'}
          {L B \prcstep{μ}{η} L B'}
          \quad
\myference{Napp2}
          {B \prcstep{μ}{η} B'}
          {B B_2 \prcstep{μ}{η} B' B_2}
          \vdbl
\myference{Ncase}
          {B \prcstep{μ}{η} B'}
          {\CASE{}{B}{x_l}{B_l}{x_r}{B_r} \prcstep{μ}{η} \CASE{}{B'}{x_l}{B_l}{x_r}{B_r}}
          \vdbl
\myference{NcaseL}
          {}
          {\CASE{}{\INL L}{x_l}{B_l}{x_r}{B_r} \prcstep{∅}{∅} B_l[x_l := L]}
          \quad
\myference{NcaseR}
          {\dots}
          {\dots}
          \vdbl
\myference{Nproj1}
          {}
          {\FST{} (\PAIR L_1 L_2) \prcstep{∅}{∅} L_1}
          \quad
\myference{Nproj2}
          {\dots}
          {\dots}
          \quad
\myference{NprojN}
          {}
          {\LOOKUP{i}{} (L_1, \dots, L_i, \dots, L_n) \prcstep{∅}{∅} L_i}
          \vdbl
\myference{Nsend1}
          {}
          {\SEND{\nonempty{p}} () \prcstep{\set{(p, ()) \mid p \in \nonempty{p}}}{∅} ⊥}
          \quad
\myference{NsendPair}
          {\SEND{\nonempty{p}} L_1 \prcstep{μ_1}{∅} ⊥ \quad
           \SEND{\nonempty{p}} L_2 \prcstep{μ_2}{∅} ⊥}
          {\SEND{\nonempty{p}} (\PAIR L_1 L_2)
           \prcstep{\set{(p, \PAIR L_1 L_2) \mid p \in \nonempty{p}}}{∅}
           ⊥}
          \vdbl
\myference{NsendInL}
          {\SEND{\nonempty{p}} L \prcstep{μ}{∅} ⊥}
          {\SEND{\nonempty{p}} (\INL L)
           \prcstep{\set{(p, \INL L) \mid p \in \nonempty{p}}}{∅}
           ⊥}
          \quad
\myference{NsendInR}
          {\dots}
          {\dots}
          \quad
\myference{NsendSelf}
          {\SEND{p} L \prcstep{μ}{∅} ⊥}
          {\SEND{p}^\ast L \prcstep{μ}{∅} L}
          \vdbl
\myference{Nrecv}
          {}
          {\RECV{p} L_0 \prcstep{∅}{\set{(p, L)}} L}
          \quad
\myference{Nequiv}
          {B \prcstep{μ}{η} B' \quad B' ≈ B''}
          {B \prcstep{μ}{η} B''}
          \vdbl
\myference{NbotApp}
          {}
          {⊥ L \prcstep{∅}{∅} ⊥}
          \quad
\myference{NbotCase}
          {}
          {\CASE{}{⊥}{x_l}{B_l}{x_r}{B_r} \prcstep{∅}{∅} ⊥}
          \vdbl
\end{gather*}

Multi-step notation is, as usual, just a convenience for proofs,
but it's worth clarifying exactly how it works.
Any $M$ zero-steps to itself with empty-set annotations.
An empty-set-annotated step can compose with any multi-step
without changing the annotation,
but steps with populated send and receive sets can _only_ compose
with empty-set-annotated multi-sets.
In other words, $B \prcstep{μ\neq ∅}{η\neq ∅}^{\ast} B'$
indicates a sequences of steps exactly one of which looks like
$B_1 \prcstep{μ}{η} B_2$
(and the rest look like $B_3 \prcstep{∅}{∅} B_4$).
That's not to say that multi-steps outside this representation are impossible
or meaningless,
I just don't think we'll need notation with which to talk about them.


\pagebreak
## Networks

A singleton network $\mathcal{N} = p[B]$
is the behavior $B$ assigned to the party/process $p$.
Parallel composition of networks is expressed as $\mathcal{N} \mid \mathcal{N}'$,
_e.g._ $⟦M⟧ = p[⟦M⟧_p] \mid q[⟦M⟧_q]$.
When many such compositons need to be expressed at once, we write
$\mathcal{N} = Π_{p \in \nonempty{p}} p[\mathcal{N}_p]$.

Network semantic steps are annotated with unpaired send actions or with $∅$;
in practice only $∅$-annotated steps are "real".
Process level semantics elevate to network level semantics
provided that the message-annotations cancel out.
The equivalence relation $≈$ lifts to networks;
I don't think we need explicit rules for that?

\begin{gather*}
\myference{Npro}
          {B \prcstep{μ}{∅} B'}
          {p[B] \netstep{p}{μ} p[B']}
          \quad
\myference{Ncom}
          {\mathcal{N} \netstep{s}{μ∪\set{(r,L)}} \mathcal{N}'
           \quad B \prcstep{∅}{\set{(s, L)}} B'}
          {\mathcal{N} \mid r[B] \netstep{s}{μ} \mathcal{N}' \mid r[B']}
          \vdbl
\myference{Nmatched}
          {\mathcal{N} \netstep{p}{∅} \mathcal{N}'}
          {\mathcal{N} \netstep{}{∅} \mathcal{N}'}
          \quad
\myference{Npar}
          {\mathcal{N} \netstep{}{∅} \mathcal{N}'}
          {\mathcal{N} \mid \mathcal{N}^{+} \netstep{}{∅} \mathcal{N}' \mid \mathcal{N}^{+}}
\end{gather*}

### Lemma "Parallelism"

> If $\mathcal{N_1} \netstep{}{∅}^{\ast} \mathcal{N_1}'$
> and $\mathcal{N_2} \netstep{}{∅}^{\ast} \mathcal{N_2}'$
> then $\mathcal{N_1} \mid \mathcal{N_2} \netstep{}{∅}^{\ast} \mathcal{N_1}' \mid \mathcal{N_2} \netstep{}{∅}^{\ast} \mathcal{N_1}' \mid \mathcal{N_2}'$.

**Proof**: This is just repeated application of \textsc{Npar}.


\pagebreak
## Endpoint projection

Following Chor-$λ$, $⟦M⟧_p$ is the projection of $M$ to $p$
and $⟦M⟧ = Π_{p \in \roles{M}} p[⟦M⟧_p]$.
If $p$ and $q$ are the only parties in $M$, then
$⟦M⟧ = p[⟦M⟧_p] \mid q[⟦M⟧_q]$.

\begin{align*}
⟦M⟧_p                        \DEF      \text{by pattern matching on $M$:}& \\
N_1 N_2                      \DEFCASE &
  \begin{cases}
    ⟦N_1⟧_p ≈ ⊥ ≈ ⟦N_2⟧_p    \DEFCASE & ⊥  \\
    \text{else}              \DEFCASE & ⟦N_1⟧_p ⟦N_2⟧_p
  \end{cases}  \\
\CASE{\nonempty{p}}{N}{x_l}{M_l}{x_r}{M_r} \DEFCASE &
  \begin{cases}
    ⟦N⟧_p ≈ ⊥                \DEFCASE & ⊥ \\
    p \in \nonempty{p}       \DEFCASE & \CASE{}{⟦N⟧_p}{x_l}{⟦M_l⟧_p}{x_r}{⟦M_r⟧_p} \\
    \text{else}              \DEFCASE & \CASE{}{⟦N⟧_p}{x_l}{⊥}{x_r}{⊥}
  \end{cases}  \\
x                            \DEFCASE &  x        \\
(λ x:T \DOT N)@\nonempty{p}  \DEFCASE &
  \begin{cases}
    p \in \nonempty{p}       \DEFCASE & λ x \DOT ⟦N⟧_p \\
    \text{else}              \DEFCASE & ⊥
  \end{cases}  \\
()@\nonempty{p}              \DEFCASE &
  \begin{cases}
    p \in \nonempty{p}       \DEFCASE & () \\
    \text{else}              \DEFCASE & ⊥
  \end{cases}  \\
\INL V                       \DEFCASE & \INL ⟦V⟧_p  &&      \\
\INR V                       \DEFCASE & \INR ⟦V⟧_p  &&      \\
\PAIR V_1 V_2                \DEFCASE & \PAIR ⟦V_1⟧_p ⟦V_2⟧_p &&         \\
(V_1, \dots, V_n)            \DEFCASE & (⟦V_1⟧_p, \dots, ⟦V_n⟧_p) &&       \\
\FST{\nonempty{p}}           \DEFCASE &
  \begin{cases}
    p \in \nonempty{p}       \DEFCASE & \FST{} \\
    \text{else}              \DEFCASE & ⊥
  \end{cases}  \\
\SND{\nonempty{p}}           \DEFCASE &
  \begin{cases}
    p \in \nonempty{p}       \DEFCASE & \SND{} \\
    \text{else}              \DEFCASE & ⊥
  \end{cases}  \\
\LOOKUP{i}{\nonempty{p}}     \DEFCASE &
  \begin{cases}
    p \in \nonempty{p}       \DEFCASE & \LOOKUP{i}{} \\
    \text{else}              \DEFCASE & ⊥
  \end{cases}  \\
\COMM{s}{\nonempty{r}}       \DEFCASE &
  \begin{cases}
    p = s, p \in \nonempty{r}      \DEFCASE & \SEND{\nonempty{r} ∖ \set{p}}^\ast \\
    p = s, p \not\in \nonempty{r}  \DEFCASE & \SEND{\nonempty{r}} \\
    p \not = s, p \in \nonempty{r} \DEFCASE & \RECV{s} \\
    \text{else}              \DEFCASE & ⊥
  \end{cases}  \\
\end{align*}


### Lemma "Cruft"

> If $Θ;∅ ⊢ M : T$ and $p \not\in Θ$,
> then $⟦M⟧_p ≈ ⊥$.

**Proof**:
By induction on the typing of $M$:

- \textsc{Tlambda}:
  $\nonempty{p} \subseteq Θ$, therefore $p \not\in \nonempty{p}$,
  therefore $⟦M⟧_p = ⊥$.
- \textsc{Tvar}: Can't happen because $M$ types with empty $Γ$.
- \textsc{Tunit}, \textsc{Tcom}, \textsc{Tproj1}, \textsc{Tproj2},
  and \textsc{TprojN}:
  Same as \textsc{Tlambda}.
- \textsc{Tpair}, \textsc{Tvec}, \textsc{Tinl}, and \textsc{Tinr}:
  In each of these cases we have some number of recursive typing judgments
  to which we can apply the inductive hypothesis.
  This enables the respective use of
  \textsc{EBpair}, \textsc{EBvec}, \textsc{EBinl}, and \textsc{EBinr}.
- \textsc{Tapp}: $M = N_1 N_2$.
  By induction, $⟦N_1⟧_p ≈ ⊥$ and $⟦N_2⟧_p ≈ ⊥$,
  so $⟦M⟧_p = ⊥$
- \textsc{Tcase}: Similar to \textsc{Tlambda},
  by induction the guard projects to $⊥$ and therefore the whole thing does too.


### Lemma "Existence"

> If $Θ;Γ ⊢ V : d@\nonempty{p}$ and $p \in \nonempty{p}$,
> then $⟦V⟧_p ≉ ⊥$.

**Proof**: By induction on possible typings of $V$:

- \textsc{Tvar}: Projection is a no-op on variables.
- \textsc{TUnit}: $⟦V⟧_p = ()$.
- \textsc{Tpair}: $p \in \nonempty{p_1} ∩ \nonempty{p_2}$,
  so it's in each of them, so we can recurse on $V_1$ and $V_2$.
- \textsc{Tinl} and \textsc{Tinr}: simple induction.


### Lemma "Values"

> **A):** $⟦V⟧_p = L$.  
> **B):** If $⟦M⟧_p = L ≉ ⊥$ then $M$ is a value $V$.

**Proof**: These are just corollaries of the definition of projection.

### Lemma "Masked"

> If $p \in \nonempty{p}$ and $V' = V \mask \nonempty{p}$
> then $⟦V⟧_p = ⟦V'⟧_p$.

**Proof**: By (inductive) case analysis of endpoint projection:

- $⟦x⟧_p = x$. By \textsc{MVvar} the mask does nothing.
- $⟦(λ x:T \DOT M)@\nonempty{q}⟧_p$:
  Since $V \mask \nonempty{p}$ is defined, by \textsc{MVlambda} it does nothing.
- $⟦()@\nonempty{q}⟧_p$: By \textsc{MVunit} $V' = )@(\nonempty{p} ∩ \nonempty{q})$.
  $p$ is in that intersection iff $p \in \nonempty{q}$,
  so the projections will both be $()$ or $⊥$ correctly.
- $\INL V_l$, $\INR V_r$, $\PAIR V_1 V_2$, $(V_1, \dots, V_n)$: simple recursion.
- $\FST{\nonempty{q}}$, $\SND{\nonempty{q}}$,
  $\LOOKUP{i}{\nonempty{q}}$, $\COMM{q}{\nonempty{q}}$:
  Since the masking is defined, it does nothing.


### Lemma "Distributive Substitution"

> If $Θ;(x : T_x) ⊢ M : T$ and $p \in Θ$,
> then $⟦M[x:=V]⟧_p = ⟦M⟧_p[x := ⟦V⟧_p]$.

**Proof**: By inductive case analysis on the form of $M$.

- $\INL V_l$, $\INR V_r$, $\PAIR V_1 V_2$, $(V_1, \dots, V_n)$: simple induction.
- $N_1 N_2$: The special case where $⟦N_1⟧_p ≈ ⟦N_2⟧_p ≈ ⊥$ must be handled
  seperately, but either way it's simple induction.
- $y$: trivial because EPP is a no-op.
- $(λ y:T_y \DOT N)@\nonempty{p}$:
  - If $p \not\in \nonempty{p}$, both sides of the equality are $⊥$.
  - If $V' = V \mask \nonempty{p}$ is defined, then  
    $⟦(λ y:T_y \DOT N)@\nonempty{p}[x:=V]⟧_p
    =⟦(λ y:T_y \DOT N[x:=V'])@\nonempty{p}⟧_p
    =  λ y \DOT ⟦N[x:=V']⟧_p$  
    and
    $⟦(λ y:T_y \DOT N)@\nonempty{p}⟧_p[x := ⟦V⟧_p]
    = (λ y \DOT ⟦N⟧_p)[x := ⟦V⟧_p]
    =  λ y \DOT (⟦N⟧_p[x := ⟦V⟧_p])
    =  λ y \DOT (⟦N⟧_p[x := ⟦V'⟧_p])$  
    (by Lemma "Masked").  
    Then we do induction on $N$ and $V'$.
  - Otherwise
    - $⟦(λ y:T_y \DOT N)@\nonempty{p}[x:=V]⟧_p = ⟦(λ y:T_y \DOT N)@\nonempty{p}⟧_p
      = λ y \DOT ⟦N⟧_p$  
      and $⟦(λ y:T_y \DOT N)@\nonempty{p}⟧_p[x := ⟦V⟧_p]
      = (λ y \DOT ⟦N⟧_p)[x := ⟦V⟧_p]
      = λ y \DOT (⟦N⟧_p[x := ⟦V⟧_p])$.
    - Since we already known $(λ y:T_y \DOT N)@\nonempty{p}[x:=V] = M$,
      we can apply Lemma "Substitution" to $M$ and unpack the typing of $M[x:=V]$
      to get $\nonempty{p};(y:T_y) ⊢ N : T'$.
    - By Lemma "Unused", we get $N[x:=V] = N$.
    - By induction on $N$ and $V$, we get $⟦N⟧_p[x := ⟦V⟧_p] = ⟦N[x:=V]⟧_p =  ⟦N⟧_p$,
      QED.
- $\CASE{\nonempty{p}}{N}{x_l}{N_l}{x_r}{N_r}$: (maybe I should work these out more?)
  - If $⟦N⟧_p ≈ ⊥$ then $⟦N[x:=V]⟧_p ≈ ⊥$ (by induction),
    so both halfs of the equality are $⊥$.
  - Else if $p \not \in \nonempty{p}$, then we get  
    $⟦\CASE{\nonempty{p}}{N[x:=V]}{x_l}{N_l'}{x_r}{N_r'}⟧_p
    = \CASE{\nonempty{p}}{⟦N[x:=V]⟧_p}{x_l}{⊥}{x_r}{⊥}$  
    and
    $⟦\CASE{\nonempty{p}}{N}{x_l}{N_l}{x_r}{N_r}⟧_p[x := ⟦V⟧_p]
    = \CASE{\nonempty{p}}{⟦N⟧_p}{x_l}{⊥}{x_r}{⊥}[x := ⟦V⟧_p]
    = \CASE{\nonempty{p}}{⟦N⟧_p[x := ⟦V⟧_p]}{x_l}{⊥}{x_r}{⊥}$,  
    which are equal by induction.
  - Else if $V' = V \mask \nonempty{p}$ is defined then we can do induction similar
    similar to how we did for the respective lambda case, except the induction is
    three-way.
  - Otherwise, it's similar to the respective lambda case, just more verbose.
- $()@\nonempty{p}$, $\FST{\nonempty{p}}$, $\SND{\nonempty{p}}$,
  $\LOOKUP{i}{\nonempty{p}}$, and $\COMM{s}{\nonempty{r}}$:
  trivial because substitution is a no-op.

### Lemma "Bottom"

> If $Θ;∅ ⊢ M : T$ and $⟦M⟧_p ≈ ⊥$ and $M \step M'$
> then $⟦M'⟧_p ≈ ⊥$.

**Proof**: By induction on the step $M \step M'$.

- \textsc{AppAbs}: $M = (λ x:T_x \DOT N)@\nonempty{p} V$,
  and necessarily $⟦(λ x:T_x \DOT N)@\nonempty{p}⟧_p ≈ ⟦V⟧_p ≈ ⊥$.
  Since the lambda doesn't project to a lambda, $p\not\in\nonempty{p}$.
  $M' = N[x:=V\mask\nonempty{p}]$.
  By \textsc{Tlambda}, Lemma "Substitution", and Lemma "Cruft",
  $⟦N[x:=V\mask\nonempty{p}]⟧_p ≈ ⊥$.
- \textsc{App1}: $M = V N$
  and necessarily $⟦V⟧_p ≈ ⟦N⟧_p ≈ ⊥$.
  By induction, $N \step N'$ and $⟦N'⟧_p ≈ ⊥$.
- \textsc{App2}: Same as \textsc{App1}.
- \textsc{Case}: The guard must project to $⊥$, so this follows from induction.
- \textsc{CaseL} (and \textsc{CaseR} by mirror image):
  $M = \CASE{\nonempty{p}}{\INL V}{x_l}{M_l}{x_r}{M_r}$
  and $M' = M_l[x_l := V\mask\nonempty{p}]$.
  Necessarily, $⟦V⟧_p ≈ ⊥$;
  by \textsc{Tcase} and \textsc{MTdata}, $N$ types as data,
  so by Lemma "Existence" $p \not\in \nonempty{p}$.
  By \textsc{Tcase}, Lemma "Substitution", and Lemma "Cruft",
  $⟦M'⟧_p = ⟦M_l[x_l := V\mask\nonempty{p}]⟧_p ≈ ⊥$.
- \textsc{Proj1}: $M = \FST{\nonempty{p}}(\PAIR V_1 V_2)$,
  and both pieces project to $⊥$.
  Therefore $p \not \in \nonempty{p}$.
  $M' = V_1 \mask \nonempty{p}$.
  Since $Θ;∅ ⊢ V_1 : T'$ (by \textsc{Tpair})
  and $T' \mask \nonempty{p} = T''$ is defined
  (by \textsc{Tapp} and the indifference of \textsc{MTdata} to the data's structure),
  by Lemma "Enclave" $\nonempty{p};∅ ⊢ V_1 \mask \nonempty{p} : T''$.
  By Lemma "Cruft" this projects to $⊥$.
- \textsc{Proj2}, \textsc{ProjN}, and \textsc{Com1} are each pretty similar to
  \textsc{Proj1}.
- \textsc{ComPair}, \textsc{ComInl}, and \textsc{ComInr} do induction among
  each other, with \textsc{Com1} as the base case.

### Lemma "Weak Completeness"

> If $Θ;∅ ⊢ M : T$ and $M \step M'$
> then $⟦M⟧_p \prcstep{μ}{η}^{\ast} B ≈ ⟦M'⟧_p$.

**Proof**: If $⟦M⟧_p ≈ ⊥$ then this is follows trivially from Lemma "Bottom",
so assume it doesn't.
We proceed with induction on form of $M \step M'$:

- \textsc{AppAbs}: $M = (λ x:T_x \DOT N)@\nonempty{p} V$,
  and $M' = N[x:=V\mask\nonempty{p}]$.
  If the lambda projects to $⊥$, then $⟦M⟧_p \prcstep{∅}{∅} ⊥$ by \textsc{NbotApp},
  and $⟦M'⟧_p ≈ ⊥$ by the same logic as the respective case of Lemma "Bottom".
  Otherwise, $p \in \nonempty{p}$
  and $⟦M⟧_p \prcstep{∅}{∅} ⟦N⟧_p[x:=⟦V⟧_p]$ by \textsc{NabsApp}.
  By Lemma "Masked" and Lemma "Distributive Substitution"
  $⟦N⟧_p[x:=⟦V⟧_p] = ⟦N⟧_p[x:=⟦V\mask\nonempty{p}⟧_p]
  = ⟦N[x:=V\mask\nonempty{p}]⟧_p = ⟦M'⟧_p$.
- \textsc{App1}: $M = V N \step V N' = M'$.
  If $⟦N⟧_p ≈ ⊥$ then the rest follows from Lemma "Bottom".
  Otherwise we use induction on $N$ to satisfy some sequence of \textsc{Napp1} steps.
  If $⟦N'⟧_p ≈ ⊥$ then a final \textsc{NbotApp} step may be needed.
- \textsc{App2}: Similar to \textsc{App1}.
- \textsc{Case}: By our assumptions, the guard can't project to $⊥$;
  we just do induction on the guard to satisfy \textsc{Ncase}.
  As in \textsc{App1}, a final use of \textsc{NappBot} may be needed.
- \textsc{CaseL} (\textsc{CaseR} mirrors):
  $M = \CASE{\nonempty{p}}{\INL V}{x_l}{M_l}{x_r}{M_r}$,
  and $⟦M⟧_p = \CASE{}{\INL ⟦V⟧_p}{x_l}{B_l}{x_r}{B_r}$.
  $⟦M⟧_p \prcstep{∅}{∅} B_l[x_l := ⟦V⟧_p]$ by \textsc{NcaseL}.
  $M' = M_l[x_l := V\mask\nonempty{p}]$.
  If $p \in \nonempty{p}$
  then $B_l = ⟦M_l⟧_p$
  and by Lemma "Masked" Lemma "Distributive Substitution"
  $B_l[x_l := ⟦V⟧_p] = ⟦M_l⟧_p[x_l := ⟦V⟧_p]
  = ⟦M_l⟧_p[x_l := ⟦V\mask\nonempty{p}⟧_p] = ⟦M'⟧_p$.
  Otherwise, $B_l[x_l := ⟦V⟧_p] = ⊥$
  and by \textsc{Tcase}, Lemma "Substitution", and Lemma "Cruft",
  $⟦M'⟧_p ≈ ⊥$.
- \textsc{Proj1}: $M = \FST{\nonempty{p}} (\PAIR V_1 V_2)$
  and $M' = V_1 \mask \nonempty{p}$.
  If $p \not\in \nonempty{p}$, then $⟦M⟧_p \prcstep{∅}{∅} ⊥$
  by \textsc{NbotApp}
  and by Lemma "Enclave" and Lemma "Cruft",
  $⟦M'⟧_p ≈ ⊥$.
  Otherwise, $⟦M⟧_p = \FST{} (\PAIR ⟦V_1⟧_p ⟦V_2⟧_p)$,
  which steps by \textsc{Nproj1} to $⟦V_1⟧_p$,
  which equals $⟦M'⟧_p$ by Lemma "Masked".
- \textsc{Proj2}, \textsc{ProjN}: Same as \textsc{Proj1}.
- \textsc{Com1}: $M = \COMM{s}{\nonempty{r}} ()@\nonempty{p}$
  and $M' = ()@\nonempty{r}$.
  - $s = p$ and $p \in \nonempty{r}$:
    By \textsc{MVunit}, $p \in \nonempty{p}$,
    so $⟦M⟧_p = \SEND{\nonempty{r} ∖ \set{p}}^{\ast} ()$,
    which steps by \textsc{NsendSelf} (using \textsc{Nsend1}) to $()$.
    $⟦M'⟧_p = ()$.
  - $s = p$ and $p \not\in \nonempty{r}$:
    By \textsc{MVunit}, $p \in \nonempty{p}$,
    so $⟦M⟧_p = \SEND{\nonempty{r}} ()$,
    which steps by \textsc{Nsend1} to $⊥$.
    $⟦M'⟧_p = ⊥$.
  - $s \neq p$ and $p \in \nonempty{r}$:
    $⟦M⟧_p = \RECV{s} ⟦()@\nonempty{p}⟧_p$,
    which can step by \textsc{Nrecv} to $⟦M'⟧_p$.
  - Otherwise, $⟦M⟧_p = ⊥ ⟦()@\nonempty{p}⟧_p$,
    which can step by \textsc{NbotApp} to $⊥ = ⟦M'⟧_p$.
- \textsc{ComPair}, \textsc{ComInl}, and \textsc{ComInr}:
  Each uses the same structure of proof as \text{Com1},
  using induction between the cases
  to support the respective process-semantics steps.


### Theorem "Completeness"

> If $Θ;∅ ⊢ M : T$ and $M \step M'$,
> then $⟦M⟧ \netstep{}{∅}^{+} \mathcal{N} ≈ ⟦M'⟧$.

**Proof**:
By case analysis on the semantic step $M \step M'$:

- \textsc{AppAbs},
  \textsc{CaseL},
  \textsc{CaseR},
  \textsc{Proj1},
  \textsc{Proj2},
  and \textsc{ProjN}:
  Necessarily, the set of parties $\nonempty{p}$ for whom $⟦M⟧ ≉ ⊥$ is not empty.
  (Do I need that as a lemma?)
  For every $p \in \nonempty{p}$,
  by Lemma "Weak Completeness" $⟦M⟧_p \prcstep{∅}{∅}^{\ast} ⟦M'⟧_p$
  (checking the cases to see that the annotations are really empty!).
  By \textsc{Npro} and \textsc{Nmatched}, each of those is also a
  (sequence of) network step(s),
  which by Lemma "Parallelism" can be composed in any order to get
  $⟦M⟧ \netstep{}{∅}^{+} \mathcal{N}$.
  For every $p \in \nonempty{p}$,
  $\mathcal{N}_p = ⟦M'⟧_p$,
  and for every $q \not\in \nonempty{p}$,
  $\mathcal{N}_q = ⟦M⟧_q ≈ ⟦M'⟧_q$,
  Q.E.D.
- \textsc{Com1},
  \textsc{ComPair},
  \textsc{ComInl},
  and \textsc{ComInr}:
  $M = \COMM{s}{\nonempty{r}} V$.
  By the recursive structure of \textsc{Com1}, \textsc{ComPair}, \textsc{ComInl},
  and \textsc{ComInr}, $M'$ is some structure of
  $\set{\PAIR, \INL{}, \INR{}, ()@\nonempty{r}}$,
  and $⟦M'⟧_{r\in\nonempty{r}} = ⟦V⟧_s$.
  For every $q \not\in \nonempty{r} ∪ \set{s}$, either $⟦M⟧_q ≈ ⊥$ or $⟦M⟧_q ≈ ⊥ L$
  which can step to $⊥ ≈ ⟦M'⟧_q$ by \textsc{NbotApp} and Lemma "Weak Completeness".
  Compose all of those to say $⟦M⟧ \netstep{}{∅}^{\ast} \mathcal{N}^q$;
  it remains to show that $\mathcal{N}^q \netstep{}{∅}^{+} \mathcal{N} ≈ ⟦M'⟧$.
  Consider two cases:
  - $s \not\in \nonempty{r}$:  
    By Lemma "Weak Completeness"
    $⟦M⟧_s = \SEND{\nonempty{r}} ⟦V⟧_s
    \prcstep{\set{(r, ⟦V⟧_s) \mid r \in \nonempty{r}}}{∅}^{\ast} ⊥$.
    By the previously mentioned structure of $M'$, $⟦M'⟧_s ≈ ⊥$.  
    For every $r \in \nonempty{r}$,
    by Lemma "Weak Completeness"
    $⟦M⟧_r = \RECV{s} ⟦V⟧_r
    \prcstep{∅}{\set{(s,⟦V⟧_s)}}^{\ast} ⟦V⟧_s = ⟦M'⟧_{r}$.  
    By \textsc{Npro},
    $s[⟦M⟧_s] \netstep{s}{\set{(r, ⟦V⟧_s) \mid r \in \nonempty{r}}} s[⊥≈⟦M'⟧_s]$.
    (For both $s$ and the parties in $\nonempty{r}$,
    they may need to take multiple process-steps,
    but only one step each will have non-empty annotations.
    I elide the empty-set-annotaed steps here for brevity;
    they can be made explicity by introducing intermediate forms.)
    This composes in parallel with each of the $r_{\in\nonempty{r}}[⟦M⟧_r]$
    by \textsc{Ncom} in any order until the unmactched send is empty
    and can be elided by \textsc{Nmatched}.
    This composes by Lemma "Parallelism" with the step to $\mathcal{N}^q$, Q.E.D.
  - $s \in \nonempty{r}$: Let $\nonempty{r_0} = \nonempty{r} ∖ \set{s}$.  
    By Lemma "Weak Completeness"
    $⟦M⟧_s = \SEND{\nonempty{r_0}}^{\ast} ⟦V⟧_s
    \prcstep{\set{(r, ⟦V⟧_s) \mid r \in \nonempty{r_0}}}{∅} ⟦V⟧_s
    = ⟦M'⟧_{s\in \nonempty{r}}$.  
    For every $r \in \nonempty{r_0}$,
    by Lemma "Weak Completeness"
    $⟦M⟧_r = \RECV{s} ⟦V⟧_r
    \prcstep{∅}{\set{(s,⟦V⟧_s)}} ⟦V⟧_s = ⟦M'⟧_{r}$.  
    We proceed as in the previous case.
- \textsc{App1} (\textsc{App2} and \textsc{Case} are similar):
  $M = V N$.
  By induction, $⟦N⟧ \netstep{}{∅}^{+} \mathcal{N} ≈ ⟦N'⟧$.
  Every step in that process which in which a single party advances locally
  can lift to an $M$ step by \textsc{Napp1}.
  For a \textsc{Ncom} step, each of the participating parties will
  also lift their $N$ step to a $M$ step by \textsc{Napp1};
  since this doesn't change the send & receive annotations,
  the cancellation will still work.
  As in the \textsc{AppAbs} case,
  parties for whom the projection is $⊥$ may have their own process steps
  which can be composed by Lemma "Parallelism".



\pagebreak

### Lemma "Weak Soundness"

> If $Θ;∅ ⊢ M : T$ and $⟦M⟧ = \mathcal{N}_0 \mid \mathcal{N}_M
> \netstep{}{∅} \mathcal{N}_1 \mid \mathcal{N}_M
> \netstep{}{∅} \dots \netstep{}{∅} \mathcal{N}_n \mid \mathcal{N}_M$
> where for every $p[\_] \in \mathcal{N}_0$ there is exactly one index $i$
> s.t. $\mathcal{N}_i(p) \neq \mathcal{N}_{i+1}(p)$,
> then $M \step M'$
> and $\mathcal{N}_M \netstep{}{∅}^{\ast} \mathcal{N}_M'$
> such that $\mathcal{N}_n \mid \mathcal{N}_M' ≈ ⟦M'⟧$.  
> (Corollary:
> $\mathcal{N}_n \mid \mathcal{N}_M \netstep{}{∅}^{\ast}
>  \mathcal{N}_n \mid \mathcal{N}_M'$)

**Proof**: **TODO!**


### Theorem "Soundness"

> If $Θ;∅ ⊢ M : T$ and $⟦M⟧ \netstep{}{∅}^{\ast} \mathcal{N}$,
> then there exists $M''$ and $\mathcal{N}''$ such that
> $M \step^{\ast} M''$, $\mathcal{N} \netstep{}{∅}^{\ast} \mathcal{N}''$,
> and $⟦M''⟧ ≈ \mathcal{N}''$.

**Proof**:
Ignore the trivial case where
$⟦M⟧ \netstep{}{∅}^{\ast} \mathcal{N}$ denotes zero steps.
Decompose the multi-step into
$⟦M⟧ = \mathcal{N}_0 \mid \mathcal{N}_M
\netstep{}{∅} \dots \netstep{}{∅} \mathcal{N}_n \mid \mathcal{N}_M
\netstep{}{∅}^{\ast} \mathcal{N}$
such that for every $p[\_] \in \mathcal{N}_0$ there is exactly one index $i$
s.t. $\mathcal{N}_i(p) \neq \mathcal{N}_{i+1}(p)$,
and $n$ is as large as possible.
(There are other ways of breaking this down, but let's require, which we can,
that $\mathcal{N}_0$ is not empty, but $\mathcal{N}_M$ might be.)

By Lemma "Weak Soundness", there exists $M'$ and $\mathcal{N}_M'$
such that $M \step M'$
and $\mathcal{N}_n \mid \mathcal{N}_M \netstep{}{∅}^{\ast}
\mathcal{N}_n \mid \mathcal{N}_M' ≈ ⟦M'⟧$.

If $⟦M⟧ \netstep{}{∅}^{\ast} \mathcal{N}$ uses only \textsc{Nequiv},
then... nothing, I don't think i need this.

Proceed by induction on the structure of $M$:

- $M = N_1 N_2$: Decompose the projection as
  $⟦M⟧ = \mathcal{N}^M_1 \mid \mathcal{N}^M_2$
  where for every $p[B_p] \in \mathcal{N}^M_1$, $B_p = ⟦N_1⟧_p ⟦N_2⟧_p$
  and for every $q[B_q] \in \mathcal{N}^M_2$, $B_q = ⊥$.  
  Consider the cases if $N_2$ is or is not a value:
  - $N_2 = V$: There are five cases



\pagebreak
## Scratch
### Lemma "Weak Soundness"

> If $Θ;∅ ⊢ M : T$ and $p \in Θ$ and $⟦M⟧_p \prcstep{μ}{η} B$
> then there exists $M'$ such that $B \prcstep{∅}{∅}^{\ast} ⟦M'⟧_p$
> and $M \step^{\ast} M'$.

**Proof**:
By induction on the step $⟦M⟧_p \prcstep{μ}{η} B$.
Note that by Lemma "Values", the observation that process values cannot step,
and Theorem "Progress", $M$ necessarily can step to _something_.

- \textsc{NabsApp}: $M = (λ x:T_x \DOT N)@\nonempty{p} V$
  and $⟦M⟧_p = (λ x \DOT ⟦N⟧_p) ⟦V⟧_p \prcstep{∅}{∅} ⟦N⟧_p[x:=⟦V⟧_p] = B$.  
  Necessarily, $⟦V⟧_p$ is a value
  (which is how we know $V$ is a value instead of some arbitrary expression,
  by Lemma "Values")
  and $p\in\nonempty{p}$.
  Therefore, $M \step N[x:=V\mask\nonempty{p}]$.  
  By Lemma "Distributive Substitution"
  $⟦N[x:=V\mask\nonempty{p}]⟧_p = ⟦N⟧_p[x:=⟦V\mask\nonempty{p}⟧_p]$
  and by Lemma "Masked" $⟦V\mask\nonempty{p}⟧_p = ⟦V⟧_p$.
  Q.E.D.
- \textsc{Napp1}: $M = V N$
  and $⟦M⟧_p = ⟦V⟧_p ⟦N⟧_p$ where $⟦N⟧_p \prcstep{μ}{η} B'$
  so that $B = ⟦V⟧_p B'$.  
  By induction on $⟦N⟧_p$ and $B'$, there exists $N'$ such that
  $B' \prcstep{∅}{∅}^{\ast} ⟦N'⟧_p$
  and $N \step^{\ast} N'$.
  Therefore, $M \step^{\ast} V N'$ by a series of \textsc{App1}.
  $V N'$ is our target $M'$.  
  If $⟦V N'⟧_p ≉ ⊥$ then $⟦M'⟧_p = ⟦V⟧_p ⟦N'⟧_p$,
  which $B$ can empty step to by further applications of \textsc{Napp1}.  
  Otherwise, $⟦M'⟧_p = ⊥ ≈ ⟦V⟧_p ≈ ⟦N'⟧_p$.
  $B'$ must first step to $⊥ ⊥$ by \textsc{Napp1} as in the other case,
  and then finish with \textsc{NbotApp}.
- \textsc{Napp2}: $M = N_1 N_2$
  and $⟦M⟧_p = ⟦N_1⟧_p ⟦N_2⟧_p$ where $⟦N_1⟧_p \prcstep{μ}{η} B'$
  so that $B = B' ⟦N_2⟧_p$.  
  By induction on $⟦N_1⟧_p$ and $B'$, there exists $N'$ s.t.
  $B' \prcstep{∅}{∅}^{\ast} ⟦N'⟧_p$
  and $N_1 \step^{\ast} N'$.
  Therefore $M \step^{\ast} N' N_2$ by a series of \textsc{App2}.
  $N' N_2$ is our target $M'$.  
  If $⟦N' N_2⟧_p ≉ ⊥$ then $⟦M'⟧_p = ⟦N'⟧_p ⟦N_2⟧_p$,
  which $B$ can empty step to by further applications of \textsc{Napp2}.  
  Otherwise, $⟦M'⟧_p = ⊥ ≈ ⟦N'⟧_p ≈ ⟦N_2⟧_p$.
  $B'$ must first step to $⊥ ⊥$ by \textsc{Napp2} as in the other case,
  and then finish with \textsc{NbotApp}.
- \textsc{Ncase}: $M = \CASE{\nonempty{p}}{N}{x_l}{M_l}{x_r}{M_r}$
  and $⟦M⟧_p = \CASE{}{⟦N⟧_p}{x_l}{B_l}{x_r}{B_r}$ where $⟦N⟧_p \prcstep{μ}{η} B'$
  so that $B = \CASE{}{B'}{x_l}{B_l}{x_r}{B_r}$.  
  By induction on $⟦N⟧_p$ and $B'$, there exists $N'$ such that
  $B' \prcstep{∅}{∅}^{\ast} ⟦N'⟧_p$
  and $N \step^{\ast} N'$.
  Therefore, $M \step^{\ast} \CASE{\nonempty{p}}{N'}{x_l}{M_l}{x_r}{M_r}$
  by a series of \textsc{Case}.
  $\CASE{\nonempty{p}}{N'}{x_l}{M_l}{x_r}{M_r}$ is our target $M'$.  
  If $⟦N'⟧_p = ⊥ = ⟦M'⟧_p$ then $B$ can empty-step to it
  by \textsc{Ncase} and \textsc{NbotCase},
  otherwise \textsc{Ncase} alone is enough.
- \textsc{NcaseL}:
  $M = \CASE{\nonempty{p}}{V}{x_l}{M_l}{x_r}{M_r}$,
  $⟦V⟧_p \neq ⊥$,  
  and $⟦M⟧_p = \CASE{}{\INL ⟦V⟧_p}{x_l}{B_l}{x_r}{B_r}
  \prcstep{∅}{∅} B_l[x := ⟦V⟧_p] = B$.  
  $M \step M_l[x_l := V \mask \nonempty{p}] = M'$ by \textsc{CaseL}.
  If $p \in \nonempty{p}$, then $B = ⟦M_l⟧_p[x := ⟦V⟧_p]$;
  the proof completes by Lemma "Masked" and Lemma "Distributive Substitution".
  Otherwise, $B_l = ⊥ = B$;
  by \textsc{Tcase}, Lemma "Substitution", and Lemma "Cruft",
  $⟦M'⟧_p ≈ ⊥$.
  **TODO:** We haven't actually shown that $B$ can step to $⟦M'⟧_p$,
  just that they're equivalent, which isn't exactly what the lemma says!
  I think the correct solution is probably to redefine EEP
  in a way that strengthens Lemma "Cruft".
  Maybe we can even get rid of the equivalence, IDK.
- \textsc{NcaseR}: Same as \textsc{NcaseL}.
- \textsc{Nproj1}, \textsc{Nproj2}, and \textsc{NprojN}:
  Basically the same as \textsc{NabsApp}.
- \textsc{Nsend1}: $M = \COMM{p}{\nonempty{r}} ()@\nonempty{p}$,
  $p \in \nonempty{p}$, $p \not\in \nonempty{r}$,
  and $⟦M⟧ = \SEND{\nonempty{p}} () \prcstep{\set{(p,()) \mid p\in\nonempty{p}}}{∅}
  ⊥ = B$.  
  $M \step ()@\nonempty{r}$ by \textsc{Com1}, which projects to $⊥$.
- \textsc{NsendPair}, \textsc{NsendInL}, \textsc{NsendInR}:
  By induction among each other with \textsc{Nsend1} as the base case.
  **Except! TODO:** this only works up to equivalence!
- \textsc{NsendSelf}: This recurses into the other $\SEND{}$ cases,
  with the difference that $p\in\nonempty{r}$,
  so the data value is unchanged by the step instead of becoming $⊥$.
  **TODO:** make this more explicit?
- \textsc{Nrecv}: **Straight up breaks the lemma!**
  because $B$ has no relation to $M$.
- \textsc{Nequiv}: 
- \textsc{NbotApp}: 
- \textsc{NbotCase}: 

**Proof**:
Consider the smallest $\nonempty{p}$ such that
$⟦M⟧ = \mathcal{N}^{+} \mid Π_{p \in \nonempty{p}} p[⟦M⟧_p]$
and $\mathcal{N} = \mathcal{N}^{+} \mid Π_{p \in \nonempty{p}} \mathcal{N}_p$.
The derivation of $⟦M⟧ \netstep{}{∅} \mathcal{N}$ must be based on
some nested applications of \textsc{Nmatched} and \textsc{Npar},
such that $Π_{p \in \nonempty{p}} p[⟦M⟧_p]
\netstep{q}{∅} Π_{p \in \nonempty{p}} \mathcal{N}_p$.
There are two ways that could be justified:

- \textsc{Npro}: $\nonempty{p} = \{q\}$.
  $⟦M⟧_q \prcstep{∅}{∅} \mathcal{N}_q$.
  We must consider every possible way it could do that:
  - \textsc{NabsApp}:
    $⟦M⟧_q = (λ x \DOT ⟦N⟧_q) L$
    and $\mathcal{N}_q = ⟦N⟧_q[x := L]$.
    Using Lemma "Values" B, $M = (λ x:T_x \DOT N)@\nonempty{r} V$,
    where  $q \in \nonempty{r}$.
    $M' = N[x := V \mask \nonempty{r}]$ by Theorem "Progress" and \textsc{AppAbs}.
    For every $r \in \nonempty{r}$ (including $q$, for whom $⟦V⟧_r = L$),
    $⟦M⟧_r = (λ x \DOT ⟦N⟧_r) ⟦V⟧_r$
    and $⟦M'⟧_r = ⟦N[x := V \mask \nonempty{r}]⟧_r
    = ⟦N⟧_r[x := ⟦V \mask \nonempty{r}⟧_r] = ⟦N⟧_r[x := ⟦V⟧_r]$
    by Lemma "Distributive Substitution" and Lemma "Masked".
    For each such $r$, $⟦M⟧_r \prcstep{∅}{∅} ⟦M'⟧_r$ by \textsc{NabsApp}.
    For every $s \not \in \nonempty{r}$,
    $⟦M⟧_s = ⊥ ⟦V⟧_s$
    and $⟦M'⟧_s = ⟦N[x := V \mask \nonempty{r}]⟧_s$
    which by Lemma "Substitution", Lemma "Cruft",
    and the original typing derivation of $M$ ... 
    **STILL A FING PENTAGON!**





