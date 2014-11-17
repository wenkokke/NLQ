------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Intuitionistic.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Type                       Univ as T hiding (module DecEq)
open import Logic.Intuitionistic.Structure Univ as S hiding (module DecEq)


infix 5 _⊢_

data Judgement  : Set ℓ where
  _⊢_ : (Γ : List Type) (A : Type) → Judgement


⊢-injective : ∀ {X Y A B} → X ⊢ A ≡ Y ⊢ B → X ≡ Y × A ≡ B
⊢-injective refl = refl , refl


module DecEq (_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)) where

  open T.DecEq _≟-Univ_ using (_≟-Type_)
  open S.DecEq _≟-Univ_ using (_≟-Structure_)

  infix 1 _≟-Judgement_

  _≟-Judgement_ : (I J : Judgement) → Dec (I ≡ J)
  X ⊢ A ≟-Judgement Y ⊢ B with A ≟-Type B | X ≟-Structure Y
  ... | yes A≡B | yes X≡Y rewrite X≡Y | A≡B = yes refl
  ... | no  A≢B | _       = no (A≢B ∘ proj₂ ∘ ⊢-injective)
  ... | _       | no  X≢Y = no (X≢Y ∘ proj₁ ∘ ⊢-injective)


  decSetoid : DecSetoid _ _
  decSetoid = P.decSetoid _≟-Judgement_
