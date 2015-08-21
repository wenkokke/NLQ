------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Logic.NLIBC.Structure.Context {ℓ} (Atom : Set ℓ) where


open import Logic.NLIBC.Structure Atom


infixr 5 _∙>_
infixl 5 _<∙_
infixr 5 _∘>_
infixl 5 _<∘_
infixl 4 _[_] _[_]ᵀ


data Context : Set ℓ where
  []    : Context
  _∙>_  : Structure → Context   → Context
  _<∙_  : Context   → Structure → Context
  _∘>_  : Structure → Context   → Context
  _<∘_  : Context   → Structure → Context


_[_] : Context → Structure → Structure
[]       [ Δ ] = Δ
Γ ∙> Γ′  [ Δ ] = Γ ∙ (Γ′ [ Δ ])
Γ <∙ Γ′  [ Δ ] = (Γ [ Δ ]) ∙ Γ′
Γ ∘> Γ′  [ Δ ] = Γ ∘ (Γ′ [ Δ ])
Γ <∘ Γ′  [ Δ ] = (Γ [ Δ ]) ∘ Γ′

_<_> : Context → Context → Context
[]       < Δ > = Δ
(q ∙> Γ) < Δ > = q ∙> (Γ < Δ >)
(Γ <∙ q) < Δ > = (Γ < Δ >) <∙ q
(q ∘> Γ) < Δ > = q ∘> (Γ < Δ >)
(Γ <∘ q) < Δ > = (Γ < Δ >) <∘ q

<>-def : (Γ Δ : Context) (p : Structure)
       → (Γ [ Δ [ p ] ]) ≡ ((Γ < Δ >) [ p ])
<>-def    []    Δ p = refl
<>-def (_ ∙> Γ) Δ p rewrite <>-def Γ Δ p = refl
<>-def (Γ <∙ _) Δ p rewrite <>-def Γ Δ p = refl
<>-def (_ ∘> Γ) Δ p rewrite <>-def Γ Δ p = refl
<>-def (Γ <∘ _) Δ p rewrite <>-def Γ Δ p = refl


data Contextᵀ : Set ℓ where
  []    : Contextᵀ
  _∙>_  : Structure → Contextᵀ  → Contextᵀ
  _<∙_  : Contextᵀ  → Structure → Contextᵀ

_[_]ᵀ : Contextᵀ → Structure → Structure
[]       [ Δ ]ᵀ = Δ
Γ ∙> Γ′  [ Δ ]ᵀ = Γ ∙ (Γ′ [ Δ ]ᵀ)
Γ <∙ Γ′  [ Δ ]ᵀ = (Γ [ Δ ]ᵀ) ∙ Γ′


unT : Contextᵀ → Context
unT    []    = []
unT (q ∙> Γ) = q ∙> unT Γ
unT (Γ <∙ q) = unT Γ <∙ q

unT-correct : (Γ : Contextᵀ) {Δ : Structure}
            → (Γ [ Δ ]ᵀ) ≡ ((unT Γ) [ Δ ])
unT-correct    []    {Δ} = refl
unT-correct (_ ∙> Γ) {Δ} rewrite unT-correct Γ {Δ} = refl
unT-correct (Γ <∙ _) {Δ} rewrite unT-correct Γ {Δ} = refl
