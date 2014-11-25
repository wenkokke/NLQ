------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Intuitionistic.CMinus1.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Type      Univ as T hiding (module DecEq)
open import Logic.Intuitionistic.Structure Type as S hiding (module DecEq)


infix 5 _⊢_∣_

data Judgement  : Set ℓ where
  _⊢_∣_ : (Γ : List Type) (A : Type) (Δ : List Type) → Judgement


⊢-injective : ∀ {X Y Z W A B} → X ⊢ A ∣ Y ≡ Z ⊢ B ∣ W → X ≡ Z × A ≡ B × Y ≡ W
⊢-injective refl = (refl , (refl , refl))


module DecEq (_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)) where

  open T.DecEq _≟-Univ_ using (_≟-Type_)
  open S.DecEq _≟-Type_ using (_≟-Structure_)

  infix 1 _≟-Judgement_

  _≟-Judgement_ : (I J : Judgement) → Dec (I ≡ J)
  X ⊢ A ∣ Y ≟-Judgement Z ⊢ B ∣ W with X ≟-Structure Z | A ≟-Type B |  Y ≟-Structure W
  ... | yes X≡Z | yes A≡B | yes Y≡W rewrite X≡Z | A≡B | Y≡W = yes refl
  ... | no  X≢Z | _       | _      = no (X≢Z ∘ proj₁ ∘ ⊢-injective)
  ... | _       | no  A≢B | _      = no (A≢B ∘ proj₁ ∘ proj₂ ∘ ⊢-injective)
  ... | _       | _       | no Y≢W = no (Y≢W ∘ proj₂ ∘ proj₂ ∘ ⊢-injective)


  decSetoid : DecSetoid _ _
  decSetoid = P.decSetoid _≟-Judgement_
