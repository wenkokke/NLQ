------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Data.Bool                             using (Bool; true; false)
open import Data.Product                          using (_×_; _,_)
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


-- specific to lambek-grishin

open import Logic.Polarity public

PolarisedUniv : Set
PolarisedUniv = Polarity × Univ

open import Logic.Translation
open import Logic.Classical.Ordered.LambekGrishin.Type                PolarisedUniv public
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised PolarisedUniv public
open import Logic.Classical.Ordered.LambekGrishin.Judgement           PolarisedUniv public
open import Logic.Classical.Ordered.LambekGrishin.Base                Univ          public hiding (PolarisedUniv)
open import Logic.Classical.Ordered.LambekGrishin.ToLinear            Univ S        using (Ord→Lin)
open import Logic.Intuitionistic.Linear.Lambda.ToUnrestricted         Univ          using (Lin→Un)
open import Logic.Intuitionistic.Unrestricted.Lambda.ToAgda           Univ ⟦_⟧ᵁ     using (Un→Agda)
open import Logic.Intuitionistic.Unrestricted.Agda.Environment                      public

open Translation (Un→Agda ◇ Lin→Un ◇ Ord→Lin) public renaming ([_] to toAgda)

np np⁻ n n⁻ s s⁻ : Type
np  = el (+ , NP)
np⁻ = el (- , NP)
n   = el (+ , N)
n⁻  = el (- , N)
s   = el (+ , S)
s⁻  = el (- , S)
