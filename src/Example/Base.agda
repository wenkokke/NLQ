------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Data.Bool                             using (Bool; true; false)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Example.Base (Entity : Set) where


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


module UsingLambdaCMinus where

  open import Logic.Translation
  open import Logic.Classical.Ordered.LambdaCMinus                          Univ public
  open import Logic.Classical.Linear.LambdaCMinus.ToUnrestricted            Univ           using (Lin→Un)
  open import Logic.Classical.Unrestricted.LambdaCMinus.ToAgda              Univ ⟦_⟧ᵁ Bool using (Un→Agda)
  open import Logic.Classical.Unrestricted.LambdaCMinus.EquivalentToIndexed Univ           using (Un→Ix)
  open import Logic.Classical.Unrestricted.LambdaCMinus.Indexed.Show        Univ public    using (showTerm; showTermWith)
  open import Logic.Intuitionistic.Unrestricted.Agda.Environment                 public

  open Translation (Un→Agda ◇ Lin→Un ◇ Ord→Lin) public
  open Translation (Un→Ix   ◇ Lin→Un ◇ Ord→Lin) public using () renaming ([_] to [_]ᴵ)


module UsingLambekGrishin where

  open import Logic.Classical.Ordered.LambekGrishin Univ public
