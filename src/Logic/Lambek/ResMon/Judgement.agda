------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Lambek.ResMon.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type Univ as T hiding (module DecEq)


infix 5 _⊢_

data Judgement : Set ℓ where
  _⊢_ : Type → Type → Judgement


⊢-injective : ∀ {A₁ A₂ B₁ B₂} → A₁ ⊢ B₁ ≡ A₂ ⊢ B₂ → A₁ ≡ A₂ × B₁ ≡ B₂
⊢-injective refl = refl , refl


module DecEq (_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)) where

  open T.DecEq _≟-Univ_ using (_≟-Type_ )

  _≟-Judgement_ : (I J : Judgement) → Dec (I ≡ J)
  (A₁ ⊢ B₁) ≟-Judgement (A₂ ⊢ B₂) with (A₁ ≟-Type A₂) | (B₁ ≟-Type B₂)
  ... | yes A₁≡A₂ | yes B₁≡B₂ rewrite A₁≡A₂ | B₁≡B₂ = yes refl
  ... | no  A₁≢A₂ | _         = no (A₁≢A₂ ∘ proj₁ ∘ ⊢-injective)
  ... | _         | no  B₁≢B₂ = no (B₁≢B₂ ∘ proj₂ ∘ ⊢-injective)


  decSetoid : DecSetoid _ _
  decSetoid = P.decSetoid _≟-Judgement_
