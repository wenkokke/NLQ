------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                              using (id; const)
open import Data.Bool                             using (Bool; true; false; not; _∧_; _∨_)
open import Data.List                             using (List; _∷_; []; map; foldr)
open import Data.Product                          using (_×_; proj₁; _,_)
open import Data.Unit                             using (⊤; tt)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Example.System.NLCL where


open import Example.System.Base


data Univ : Set where

  N  : Univ
  DP : Univ
  S  : Univ

  I  : Univ
  L  : Univ
  R  : Univ


_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)
N  ≟-Univ N  = yes refl
N  ≟-Univ DP = no (λ ())
N  ≟-Univ S  = no (λ ())
N  ≟-Univ I  = no (λ ())
N  ≟-Univ L  = no (λ ())
N  ≟-Univ R  = no (λ ())
DP ≟-Univ N  = no (λ ())
DP ≟-Univ DP = yes refl
DP ≟-Univ S  = no (λ ())
DP ≟-Univ I  = no (λ ())
DP ≟-Univ L  = no (λ ())
DP ≟-Univ R  = no (λ ())
S  ≟-Univ N  = no (λ ())
S  ≟-Univ DP = no (λ ())
S  ≟-Univ S  = yes refl
S  ≟-Univ I  = no (λ ())
S  ≟-Univ L  = no (λ ())
S  ≟-Univ R  = no (λ ())
I  ≟-Univ N  = no (λ ())
I  ≟-Univ DP = no (λ ())
I  ≟-Univ S  = no (λ ())
I  ≟-Univ I  = yes refl
I  ≟-Univ L  = no (λ ())
I  ≟-Univ R  = no (λ ())
L  ≟-Univ N  = no (λ ())
L  ≟-Univ DP = no (λ ())
L  ≟-Univ S  = no (λ ())
L  ≟-Univ I  = no (λ ())
L  ≟-Univ L  = yes refl
L  ≟-Univ R  = no (λ ())
R  ≟-Univ N  = no (λ ())
R  ≟-Univ DP = no (λ ())
R  ≟-Univ S  = no (λ ())
R  ≟-Univ I  = no (λ ())
R  ≟-Univ L  = no (λ ())
R  ≟-Univ R  = yes refl


⟦_⟧ᵁ : Univ → Set
⟦ N  ⟧ᵁ = Entity → Bool
⟦ DP ⟧ᵁ = Entity
⟦ S  ⟧ᵁ = Bool
⟦ _  ⟧ᵁ = ⊤

-- * import focused Lambek-Grishin calculus
open import Logic.Intuitionistic.Ordered.NLCL Univ public
