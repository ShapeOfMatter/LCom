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
\newcommand{\roles}{\mathtt{roles}}
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

From here on we will assume that bound variables are unique.
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
TODO: these rules can't fail, so reorganize this
to not be in the format of inference rules.
There are non-shadowing cases where substitution is forced to a no-op;
I think the Lemma "Substitution" suffices to show that that's ok.

\begin{gather*}
\myference{Svar0}
          {y ≢ x}
          {y[x := V] \DEF y}
          \quad
\myference{Svar1}
          {y ≡ x}
          {y[x := V] \DEF V}
          \quad
\myference{Sapp}
          {M' = M[x:=V] \quad N' = N[x:=V]}
          {(M N)[x:=V] \DEF M' N'}
          \vdbl
\myference{Slambda}
          {M' = {\begin{cases}
                M[x:=V'] & V' = V \mask \nonempty{p} \\
                M & \text{otherwise}
                \end{cases}}}
          {((λ y:T \DOT M)@\nonempty{p})[x:=V] \DEF (λ y:T \DOT M')@\nonempty{p}}
          \vdbl
\myference{Scase}
          {M' = M[x:=V] \quad
           M_l', M_r' = {\begin{cases}
                         M_l[x:=V'],M_r[x:=V'] & V' = V \mask \nonempty{p} \\
                         M_l,M_r & \text{otherwise}
                         \end{cases}}}
          {(\CASE{\nonempty{p}}{M}{x_l}{M_l}{x_r}{M_r})[x:=V] \DEF
            \CASE{\nonempty{p}}{M'}{x_l}{M_l'}{x_r}{M_r'})}
          \vdbl
\myference{SinL}
          {V_1' = V_1[x:=V]}
          {(\INL V_1)[x:=V] \DEF \INL V_1'}
          \quad
\myference{SinR}
          {V_1' = V_1[x:=V]}
          {(\INR V_1)[x:=V] \DEF \INR V_1'}
          \vdbl
\myference{Spair}
          {V_1' = V_1[x:=V] \quad V_2' = V_2[x:=V]}
          {(\PAIR V_1 V_2)[x:=V] \DEF \PAIR V_1' V_2'}
          \quad
\myference{Svec}
          {V_1' = V_1[x:=V] \quad \dots \quad V_n' = V_n[x:=V]}
          {(V_1, \dots, V_n)[x:=V] \DEF (V_1', \dots, V_n')}
          \vdbl
\myference{Sunit}
          {}
          {(()@\nonempty{p})[x:=V] \DEF ()@\nonempty{p}}
          \quad
\myference{Sproj1}
          {}
          {(\FST{\nonempty{p}})[x:=V] \DEF \FST{\nonempty{p}}}
          \quad
\myference{Sproj2}
          {}
          {(\SND{\nonempty{p}})[x:=V] \DEF \SND{\nonempty{p}}}
          \vdbl
\myference{SprojN}
          {}
          {(\LOOKUP{\nonempty{p}}{i})[x:=V] \DEF \LOOKUP{\nonempty{p}}{i}}
          \quad
\myference{Scom}
          {}
          {(\COMM{s}{\nonempty{r}})[x:=V] \DEF \COMM{s}{\nonempty{r}}}
\end{gather*}

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
          {((λ x:T \DOT M)\nonempty{p}) N \step ((λ x:T \DOT M)\nonempty{p}) N'}
          \quad
\myference{App2}
          {M \step M'}
          {M N \step M' N}
          \vdbl
\myference{Case}
          {N \step N'}
          {\CASE{\nonempty{p}}{N}{x_l}{M_l}{x_r}{M_r} \step \CASE{\nonempty{p}}{N'}{x_l}{M_l}{x_r}{M_r}}
          \vdbl
\myference{CaseL}
          {V' = V \mask \nonempty{p} \quad
           M_l' = M_l[x := V']}
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
Following their style, $⟦M⟧_p$ is the projection of $M$ to $p$,
and $\mathcal{N} = p[B]$ is the behavior $B$ assigned to the party $p$.
If $p$ and $q$ are the only parties in $M$, then we leave off the subscript to say
$⟦M⟧ = p[⟦M⟧_p] \mid q[⟦M⟧_q]$.
When many such compositons need to be expressed at once, we write
$⟦M⟧ = \mathcal{N} = Π_{p \in \roles{M}} p[⟦M⟧_p]$.

\begin{align*}
B \BNF   & L
             && \text{Process expressions are distinguished as $B$ instead of $M$.} \\
  \BNFOR & B B                && \text{}  \\
  \BNFOR & \CASE{}{B}{x}{B}{x}{B} && \text{} \\
L \BNF   & x
             && \text{Process values are distinguished as $L$ instead of $V$.} \\
  \BNFOR & λ x : T \DOT B     && \text{} \\
  \BNFOR & \INL L \BNFOR \INR L \BNFOR \FST{} \BNFOR \SND{} && \text{} \\
  \BNFOR & \PAIR L L          \BNFOR ()       && \text{} \\
  \BNFOR & \RECV{p} \BNFOR \SEND{\nonempty{p}} \BNFOR \SEND{\nonempty{p}}^\ast
             && \text{receive from one party, send to many,
                      send to many \textit{and} keep for oneself} \\
  \BNFOR & ⊥                  && \text{"missing" (someplace else)} \\
T \BNF   & T → T \BNFOR T + T \BNFOR T × T \BNFOR  ()
             && \text{Types are pretty normal.} \\
  \BNFOR & ⊥                  && \text{"someone else's problem"}
\end{align*}

I think we can skip typing of process terms, and go directly to semantics.
Semantic steps are labeled with send ($⊕$) and receive ($⊖$) sets, like so:
$B \prcstep{\set{(p,L_1), (q,L_2)}}{\set{(r, L_3), (s, L_4)}} B'$,
or $B \prcstep{μ}{η} B'$ for short.

\begin{gather*}
\myference{NabsApp}
          {}
          {(λ x : T \DOT B) L \prcstep{∅}{∅} B[x:=L]}
          \quad
\myference{Napp1}
          {B \prcstep{μ}{η} B'}
          {(λ x : T \DOT B_0) B \prcstep{μ}{η} (λ x : T \DOT B_0) B'}
          \quad
\myference{Napp2}
          {B \prcstep{μ}{η} B'}
          {B B_2 \prcstep{μ}{η} B' B_2}
          \vdbl
\myference{Nsend1A}
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
          {\RECV{p} \prcstep{∅}{\set{(p, L)}} L}
\end{gather*}

Network semantic steps are annotated with unpaired send actions, or with $∅$.
Process level semantics elevate to network level semantics
provided that the message-annotations cancel out.

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
