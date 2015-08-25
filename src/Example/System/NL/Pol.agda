------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level                                 using (zero)
open import Data.Product                          using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Traversable                      using (module RawTraversable)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


module Example.System.NL.Pol where


open import Example.System.Base public
open import Logic.Polarity      public
open import Logic.NL.Pol   Atom public


_≟-PolarisedAtom_ : (A B : Polarity × Atom) → Dec (A ≡ B)
(p , A) ≟-PolarisedAtom (q , B) with p ≟-Polarity q | A ≟-Atom B
... | yes p=q | yes A=B rewrite p=q | A=B = yes refl
... | no  p≠q | _       = no (λ x → p≠q (cong proj₁ x))
... | _       | no  A≠B = no (λ x → A≠B (cong proj₂ x))


⟦_⟧ᴾ : Polarity × Atom → Set
⟦ p , A ⟧ᴾ = ⟦ A ⟧ᴬ


open import Logic.Grammar public
open import Logic.NL.Pol.ProofSearch (Polarity × Atom) proj₁ _≟-PolarisedAtom_ public
open import Logic.NL.Pol.ToAgda (Polarity × Atom) ⟦_⟧ᴾ Bool proj₁ public

open RawTraversable (rawTraversable {zero}) using (_<$>_)


s n np inf pp iv tv : Type
s   = el (- , S)
n   = el (+ , N)
np  = el (+ , NP)
inf = el (+ , INF)
pp  = el (+ , PP)
iv  = np ⇒ s
tv  = iv ⇐ np


private
  flatten : Struct Type → Structure +
  flatten ·  A  · = ·  A  ·
  flatten ⟨  X  ⟩ = flatten X
  flatten (X , Y) = flatten X ⊗ flatten Y

  combine : (Γ : Struct (Σ Type ⟦_⟧⁺)) → ⟦ flatten (proj₁ <$> Γ) ⟧ˢ
  combine ·  p  · = proj₂ p
  combine ⟨  Γ  ⟩ = combine Γ
  combine (Γ , Δ) = combine Γ , combine Δ


instance
  grammar : Grammar
  grammar = record
    { Type           = Type
    ; Struct         = Struct
    ; rawTraversable = rawTraversable
    ; _⊢_            = λ Γ B → fNL (flatten Γ ⊢[ B ])
    ; findAll        = λ Γ B → findAll (flatten Γ ⊢[ B ])
    ; s              = s
    ; ⟦_⟧ᵗ           = ⟦_⟧⁺
    ; ⟦_⟧            = λ Γ f → ⟦ f ⟧ (combine Γ)
    }


-- -}
-- -}
-- -}
-- -}
-- -}
