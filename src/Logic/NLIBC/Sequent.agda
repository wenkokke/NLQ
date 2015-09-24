------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.NLIBC.Sequent {ℓ} (Atom : Set ℓ) where


open import Logic.NLIBC.Type      Atom as T hiding (module DecEq)
open import Logic.NLIBC.Structure Atom as S hiding (module DecEq)


infix 3 _⊢_


data Sequent : Set ℓ where
  _⊢_ : (Γ : Structure) (p : Type) → Sequent


-- Proofs which show that constructors of types (as all Agda
-- data-constructors) respect equality.
⊢-injective : ∀ {Γ Δ p q} → (Γ ⊢ p) ≡ (Δ ⊢ q) → Γ ≡ Δ × p ≡ q
⊢-injective refl = refl , refl


-- Proof that if the given universe has decidable equality, then so do types.
module DecEq (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)) where

  open T.DecEq _≟-Atom_ using (_≟-Type_)
  open S.DecEq _≟-Atom_ using (_≟-Structure_)

  infix 4 _≟-Sequent_

  _≟-Sequent_ : (J₁ J₂ : Sequent) → Dec (J₁ ≡ J₂)
  (Γ ⊢ p) ≟-Sequent (Δ ⊢ q) with Γ ≟-Structure Δ | p ≟-Type q
  ... | yes Γ=Δ | yes p=q rewrite Γ=Δ | p=q = yes refl
  ... | no  Γ≠Δ | _       = no (λ x → Γ≠Δ (proj₁ (⊢-injective x)))
  ... | _       | no  p≠q = no (λ x → p≠q (proj₂ (⊢-injective x)))

  instance
    decSetoid : DecSetoid _ _
    decSetoid = P.decSetoid _≟-Sequent_
