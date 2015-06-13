------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Data.List                                  using (List; _∷_; [])
open import Data.List.Properties                       using () renaming (∷-injective to ,-injective)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (module DecSetoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Intuitionistic.Unrestricted.Lambda.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Unrestricted.Lambda.Type Univ as T hiding (module DecEq)


infix 3 _⊢_


data Judgement : Set ℓ where
  _⊢_ : List Type → Type → Judgement


⊢-injective : ∀ {A B C D} → (A ⊢ B) ≡ (C ⊢ D) → A ≡ C × B ≡ D
⊢-injective refl = (refl , refl)


module DecEq (_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)) where


  module TEQ = T.DecEq _≟-Univ_
  open DecSetoid TEQ.decSetoid


  _≟-Types_ : (Γ Δ : List Type) → Dec (Γ ≡ Δ)
  []      ≟-Types []      = yes P.refl
  []      ≟-Types (B ∷ Δ) = no (λ ())
  (A ∷ Γ) ≟-Types []      = no (λ ())
  (A ∷ Γ) ≟-Types (B ∷ Δ)
    with A ≟ B | Γ ≟-Types Δ
  ...| yes A=B | yes Γ=Δ = yes (P.cong₂ _∷_ A=B Γ=Δ)
  ...| no  A≠B | _       = no (A≠B ∘ proj₁ ∘ ,-injective)
  ...| _       | no  Γ≠Δ = no (Γ≠Δ ∘ proj₂ ∘ ,-injective)


  _≟-Judgement_ : (I J : Judgement) → Dec (I ≡ J)
  (Γ ⊢ A) ≟-Judgement (Δ ⊢ B) with Γ ≟-Types Δ | A ≟ B
  ...| yes Γ=Δ | yes A=B = yes (P.cong₂ _⊢_ Γ=Δ A=B)
  ...| no  Γ≠Δ | _       = no (Γ≠Δ ∘ proj₁ ∘ ⊢-injective)
  ...| _       | no  A≠B = no (A≠B ∘ proj₂ ∘ ⊢-injective)


  decSetoid : DecSetoid _ _
  decSetoid = P.decSetoid _≟-Judgement_
