open import Data.Bool                             using (Bool; true; false)
open import Data.Nat                              using (suc; zero) renaming (ℕ to Entity)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Example.Base where


data Univ : Set where
  N  : Univ
  NP : Univ
  S  : Univ


_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)
N  ≟-Univ N  = yes refl
N  ≟-Univ NP = no (λ ())
N  ≟-Univ S  = no (λ ())
NP ≟-Univ N  = no (λ ())
NP ≟-Univ NP = yes refl
NP ≟-Univ S  = no (λ ())
S  ≟-Univ N  = no (λ ())
S  ≟-Univ NP = no (λ ())
S  ≟-Univ S  = yes refl


⟦_⟧ᵁ : Univ → Set
⟦ N  ⟧ᵁ = Entity → Bool
⟦ NP ⟧ᵁ = Entity
⟦ S  ⟧ᵁ = Bool

