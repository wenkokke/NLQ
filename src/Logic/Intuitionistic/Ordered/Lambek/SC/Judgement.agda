------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements the axioms and some derived inference rules.
------------------------------------------------------------------------


open import Data.Product                          using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Logic.Intuitionistic.Ordered.Lambek.SC.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Ordered.Lambek.Type         Univ as T
open import Logic.Intuitionistic.Ordered.Lambek.Type.Context Univ as TC
open TC.Simple using (_[_]; _<_>; <>-assoc; <>-def)


infix 3 _⊢_ ⊢ᴺ_ ⊢ᴾ_

data Judgement : Set ℓ where
  _⊢_ : Type → Type → Judgement
  ⊢ᴺ_ : Context → Judgement
  ⊢ᴾ_ : Context → Judgement

{-
⊢-injective : ∀ {A B C D} → A ⊢ B ≡ C ⊢ D → A ≡ C × B ≡ D
⊢-injective refl = refl , refl

⊢ᴺ-injective : ∀ {Γ₁ Γ₂} → ⊢ᴺ Γ₁ ≡ ⊢ᴺ Γ₂ → Γ₁ ≡ Γ₂
⊢ᴺ-injective refl = refl

⊢ᴾ-injective : ∀ {Δ₁ Δ₂} → ⊢ᴾ Δ₁ ≡ ⊢ᴾ Δ₂ → Δ₁ ≡ Δ₂
⊢ᴾ-injective refl = refl
-}
