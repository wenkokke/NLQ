``` hidden
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module quantifier_raising (Atom : Set) where

infixr 30 _⇒_ _⇨_
infixl 30 _⇐_ _⇦_
infixr 20 _∙_
infixr 20 _∘_
infix  3  _⊢_
```

## Quantifier Raising as structural rule


```
data Type : Set where
  el  : Atom → Type
  _⇒_ : Type → Type → Type
  _⇐_ : Type → Type → Type
  _⇨_ : Type → Type → Type
  _⇦_ : Type → Type → Type
```

```
data Structure : Set where
  ·_·  : Type      → Structure
  _∙_  : Structure → Structure → Structure
  _∘_  : Structure → Structure → Structure
  I    : Structure
  B    : Structure
  C    : Structure
```

```
data Sequent : Set where
  _⊢_ : Structure → Type → Sequent
```

``` hidden
open import Logic.NLIBC.Structure.Context Atom
     using (module Composable; Composable; Pluggable)
```
```
data Context : Set where
  []    : Context
  _∙>_  : Structure → Context   → Context
  _<∙_  : Context   → Structure → Context
  _∘>_  : Structure → Context   → Context
  _<∘_  : Context   → Structure → Context
```
```
_[_] : Context → Structure → Structure
[]        [ Δ ] = Δ
(Γ ∙> Γ′) [ Δ ] = Γ ∙ (Γ′ [ Δ ])
(Γ <∙ Γ′) [ Δ ] = (Γ [ Δ ]) ∙ Γ′
(Γ ∘> Γ′) [ Δ ] = Γ ∘ (Γ′ [ Δ ])
(Γ <∘ Γ′) [ Δ ] = (Γ [ Δ ]) ∘ Γ′
```
```
_<_> : Context → Context → Context
[]       < Δ > = Δ
(q ∙> Γ) < Δ > = q ∙> (Γ < Δ >)
(Γ <∙ q) < Δ > = (Γ < Δ >) <∙ q
(q ∘> Γ) < Δ > = q ∘> (Γ < Δ >)
(Γ <∘ q) < Δ > = (Γ < Δ >) <∘ q
```
``` hidden
<>-def : ∀ Γ Δ p → (Γ [ Δ [ p ] ]) ≡ ((Γ < Δ >) [ p ])
<>-def    []    Δ p = refl
<>-def (_ ∙> Γ) Δ p rewrite <>-def Γ Δ p = refl
<>-def (Γ <∙ _) Δ p rewrite <>-def Γ Δ p = refl
<>-def (_ ∘> Γ) Δ p rewrite <>-def Γ Δ p = refl
<>-def (Γ <∘ _) Δ p rewrite <>-def Γ Δ p = refl
```

[compute](Example/System/NLIBC.agda "((quote ax) ∷ (quote ⇒ᴸ) ∷ (quote ⇒ᴿ) ∷ (quote ⇐ᴸ) ∷ (quote ⇐ᴿ) ∷ (quote ⇨ᴸ) ∷ (quote ⇨ᴿ) ∷ (quote ⇦ᴸ) ∷ (quote ⇦ᴿ) ∷ (quote Iᵢ) ∷ (quote Iₑ) ∷ (quote Bᵢ) ∷ (quote Bₑ) ∷ (quote Cᵢ) ∷ (quote Cₑ) ∷ []) asMathParOf (quote NL_)")



[compute](Example/System/NLIBC.agda "((quote ⇨ᴿgᴸ) ∷ (quote ⇨ᴿgᴿ) ∷ []) asMathParOf (quote NL_)")
