------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level                                 using (zero)
open import Data.Product                          using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Traversable                      using (module RawTraversable)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Reflection                            using (Name)


module Example.System.LG.Pol where


open import Example.System.Base public
open import Logic.Polarity public
open import Logic.LG.Pol PolarisedAtom Polarityᴬ? public
open import Logic.Grammar public
open import Logic.LG.Pol.ProofSearch PolarisedAtom Polarityᴬ? _≟-PolarisedAtom_ public
open import Logic.LG.Pol.ToAgda PolarisedAtom ⟦_⟧ᴾ Bool Polarityᴬ? public
open ListOf ((Bool → Bool) → Bool) public

open RawTraversable (rawTraversable {zero}) using (_<$>_)


Structure⁺ = Structure +
Structure⁻ = Structure -


s n np inf pp iv tv : Type
s   = el (S   ⁻)
n   = el (N   ⁺)
np  = el (NP  ⁺)
inf = el (INF ⁺)
pp  = el (PP  ⁺)
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
    ; _⊢_            = λ Γ B → fLG (flatten Γ) ⊢[ B ]
    ; findAll        = λ Γ B → findAll (flatten Γ ⊢[ B ])
    ; s              = s
    ; ⟦_⟧ᵗ           = ⟦_⟧⁺
    ; ⟦_⟧            = λ Γ f → ⟦ f ⟧ (combine Γ)
    }
