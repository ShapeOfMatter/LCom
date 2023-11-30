---
---

Concept:

```Choreography
let a = Inl ()@R : (()@R + ()@R)
case a of
  Inl _ ⇒ Inl ()@S
  Inr _ ⇒ Inr ()@S
```

Implementation:

```chorλ
M =
(λ a : (()@R + ()@R)
    . case a of
        Inl _ ⇒ Inl ()@S;
        Inr _ ⇒ Inr ()@S
) (Inl ()@R)
```

Typing:

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

Projections:

```network
[[M]]_R = [[ ( λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S )    (Inl ()@R) ]]_R
        = [[ λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S ]]_R [[ Inl ()@R ]]_R      <first case of application.
        = [[ λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S ]]_R    Inl [[ ()@R ]]_R   <first case of inl(V).
        = [[ λ a : (()@R + ()@R) . case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S ]]_R    Inl ()             <first case of unit.
        = ⊥                                                                             Inl ()             <second case of abstraction?

--alt:  =    λ a                 . [[ case a of Inl _ ⇒ Inl ()@S; Inr _ ⇒ Inr ()@S ]]_R    Inl ()          <first case of abstraction?
        = ...

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
