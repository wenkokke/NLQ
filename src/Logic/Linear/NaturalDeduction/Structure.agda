------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.List as List using ()
open import Data.List.Properties as ListProp using ()
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Linear.NaturalDeduction.Structure {ℓ} (Univ : Set ℓ) where


open import Logic.Linear.Type Univ as T hiding (module DecEq)


open List public using (List; _++_) renaming ([] to ∅; _∷_ to _,_; _∷ʳ_ to _,′_)
open ListProp public using () renaming (∷-injective to ,-injective)


module DecEq (_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)) where

  open T.DecEq _≟-Univ_ using (_≟-Type_)

  infix 1 _≟-Structure_

  _≟-Structure_ : (X Y : List Type) → Dec (X ≡ Y)
  ∅     ≟-Structure ∅     = yes refl
  ∅     ≟-Structure B , Y = no (λ ())
  A , X ≟-Structure ∅     = no (λ ())
  A , X ≟-Structure B , Y with A ≟-Type B | X ≟-Structure Y
  ... | yes A≡B | yes X≡Y rewrite X≡Y | A≡B = yes refl
  ... | no  A≢B | _       = no (A≢B ∘ proj₁ ∘ ,-injective)
  ... | _       | no  X≢Y = no (X≢Y ∘ proj₂ ∘ ,-injective)

  decSetoid : DecSetoid _ _
  decSetoid = P.decSetoid _≟-Structure_
