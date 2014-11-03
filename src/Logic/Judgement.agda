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


module Logic.Judgement {ℓ₁ ℓ₂} (Anta : Set ℓ₁) (Succ : Set ℓ₂) where


infix 5 _⊢_

data Judgement : Set (ℓ₁ ⊔ ℓ₂) where
  _⊢_ : Anta → Succ → Judgement


⊢-injective : ∀ {A₁ A₂ S₁ S₂} → A₁ ⊢ S₁ ≡ A₂ ⊢ S₂ → A₁ ≡ A₂ × S₁ ≡ S₂
⊢-injective refl = refl , refl


module DecEq
       (_≟-Anta_ : (X Y : Anta) → Dec (X ≡ Y))
       (_≟-Succ_ : (X Y : Succ) → Dec (X ≡ Y)) where


  _≟-Judgement_ : (I J : Judgement) → Dec (I ≡ J)
  (A₁ ⊢ S₁) ≟-Judgement (A₂ ⊢ S₂) with (A₁ ≟-Anta A₂) | (S₁ ≟-Succ S₂)
  ... | yes A₁≡A₂ | yes S₁≡S₂ rewrite A₁≡A₂ | S₁≡S₂ = yes refl
  ... | no  A₁≢A₂ | _         = no (A₁≢A₂ ∘ proj₁ ∘ ⊢-injective)
  ... | _         | no  S₁≢S₂ = no (S₁≢S₂ ∘ proj₂ ∘ ⊢-injective)


  decSetoid : DecSetoid _ _
  decSetoid = P.decSetoid _≟-Judgement_
