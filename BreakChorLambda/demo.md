---
title: "Manually typing good and/or bad choreographies"
author: Mako Bates
date: 2023-11-30
refers-to: "Functional Choreographic Programming \
            Luís Cruz-Filipe, Eva Graversen, Lovro Lugović, Fabrizio Montesi, Marco Peressotti \
            2023-08-17, https://arxiv.org/abs/2111.03701"
---

### Concept

Here's a simple choreography that is broken; party `S` doesn't have the value `a`,
so doesn't know if its final valuation should be `Inl` or `Inr`.
```Choreography
let a = Inl ()@R : (()@R + ()@R)
case a of
  Inl _ ⇒ Inl ()@S
  Inr _ ⇒ Inr ()@S
```

### Implementation

Chorλ can _express_ this easily; the only change here is that we use abstraction/application instead of a let-binding.
```chorλ
M =
(λ a : (()@R + ()@R)
    . case a of
        Inl _ ⇒ Inl ()@S;
        Inr _ ⇒ Inr ()@S
) (Inl ()@R)
```

### Typing

AFAICT this choreography types just fine as `()@S + ()@S`.
Encoding a full derivation tree here sounds hard, but I've noted the types of each sub-term involved, and the applicable rule.
These sub-term types are needed during projection.
```chorλ
M                         :: ()@S + ()@S           TAPP
=
(λ a : (()@R + ()@R).
    (case
     a                    :: ()@R + ()@R           TVAR
     of
        Inl _ ⇒
            Inl ()@S;     :: ()@S + ()@S           TINR
        Inr _ ⇒
            Inr ()@S      :: ()@S + ()@S           TINR
    )                     :: ()@S + ()@S           TCASE
)                         :: (()@R + ()@R) →{} (()@S + ()@S)    TABS
(
Inl ()@R                  :: ()@R + ()@R           TINL
)
```

### Centralized Semantics

The program `M` evaluates just fine under the primary semantic model.
```chorλ
       (λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S) (Inl ()@R)
-τ,∅→                case (Inl ()@R) of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S                             APPABS
-τ,∅→                                           Inl ()@S                                               CASEL
```

### Projections

Projecting `M` to `S` fails when it tries to merge `Inl ()` with `Inr ()`.
There's also some ambiguity in how the rules for projection to `R` are supposed to work.
In the projection rule for abstractions, does _"type(x : T . M)"_ mean _"the type of M when `x:T`"_,
or is it supposed to say _"type(λ x : T . M)"_?
```network
[[M]]_R = [[ ( λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S )    (Inl ()@R) ]]_R
        = [[ λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S ]]_R [[ Inl ()@R ]]_R      <first case of application.
        = [[ λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S ]]_R    Inl [[ ()@R ]]_R   <first case of inl(V).
        = [[ λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S ]]_R    Inl ()             <first case of unit.
        = ⊥                                                                             Inl ()             <second case of abstraction?

--alt:  =    λ a                 . [[ case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S ]]_R    Inl ()          <first case of abstraction?
        =    λ a                 . case [[a]]_R of Inl _ ⇒ [[Inl ()@S]]_R; Inr _ ⇒ [[Inr ()@S]]_R  Inl ()  <first case of case.
        =    λ a                 .    case a of Inl _ ⇒ [[Inl ()@S]]_R; Inr _ ⇒ [[Inr ()@S]]_R  Inl ()     <first case of var.
        =    λ a                 .    case a of Inl _ ⇒ ⊥       ; Inr _ ⇒ ⊥                Inl ()          <second cases of inl(V) and inr(V).


[[M]]_S = [[ ( λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S )    (Inl ()@R) ]]_S
        = [[ λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S ]]_S [[ Inl ()@R ]]_S      <first case of application.
        = [[ λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S ]]_S    ⊥                  <second case of inl(V).
        =    λ a                 . [[ case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S ]]_S    Inl ()          <first case of abstraction.
        =    λ a                 .                   [[ Inl ()@S ]]_S ⊔ [[ Inr ()@S ]]_S   Inl ()          <forth case of case.
        =    λ a                 .                   [[ Inl ()@S ]]_S ⊔    Inr [[ ()@S ]]_S Inl ()         <first case of inr(V).
        =    λ a                 .                   [[ Inl ()@S ]]_S ⊔    Inr ()          Inl ()          <first case of unit.
        =    λ a                 .                      Inl [[ ()@S ]]_S ⊔ Inr ()          Inl ()          <first case of inl(V).
        =    λ a                 .                      Inl ()        ⊔    Inr ()          Inl ()          <first case of unit.
        =  ( λ a                 .                      Inl ()        ⊔    Inr ()     )  ( Inl () )        <add parens back.
                                                                      -- FAILS!
```
