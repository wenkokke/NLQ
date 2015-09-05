--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Sequent.agda
--------------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (module DecSetoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.MM96.ResMon.Sequent {ℓ} (Atom : Set ℓ) where


open import Logic.MM96.Type Atom as T hiding (module DecEq)


infix  3  _⊢_
data Sequent : Set ℓ where
  _⊢_ : Type → Type → Sequent


open import Algebra.FunctionProperties {A = Sequent} _≡_




⊢-injective : ∀ {A B C D} → (A ⊢ B) ≡ (C ⊢ D) → A ≡ C × B ≡ D
⊢-injective refl = refl , refl


module DecEq (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)) where


  module TEQ = T.DecEq _≟-Atom_
  open DecSetoid TEQ.decSetoid


  _≟-Sequent_ : (I J : Sequent) → Dec (I ≡ J)
  (A ⊢ B) ≟-Sequent (C ⊢ D) with A ≟ C | B ≟ D
  ...| yes A=C | yes B=D = yes (P.cong₂ _⊢_ A=C B=D)
  ...| no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⊢-injective)
  ...| _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⊢-injective)


  decSetoid : DecSetoid _ _
  decSetoid = P.decSetoid _≟-Sequent_
