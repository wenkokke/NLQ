open import Function
open import Data.Bool                             using (Bool; true; false; _∧_)
open import Data.Fin                              using (Fin; suc; zero; #_; toℕ)
open import Data.List                             using (List; map; foldr; _++_) renaming ([] to ∅; _∷_ to _,_)
open import Data.Nat                              using (ℕ; suc; zero)
open import Data.Product                          using (_,_)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Example.Lexicon

module Example.QuantifierRaising where

EVERYONE₁ : Type
EVERYONE₁ = ((el NP ⇐ el N) ⊗ el N)
everyone₁ : ⟦ EVERYONE₁ ⟧ᵀ
everyone₁ = (λ k → k ((λ p₁ p₂ → forallₑ (λ x → p₂ x ⊃ p₁ x)) , person))

SOMEONE₁ : Type
SOMEONE₁ = ((el NP ⇐ el N) ⊗ el N)
someone₁ : ⟦ SOMEONE₁ ⟧ᵀ
someone₁ = (λ k → k ((λ p₁ p₂ → existsₑ (λ x → p₂ x ∧ p₁ x)) , person))

JOHN_LOVES_MARY : λC⁻ · JOHN · ⊗ (· LOVES · ⊗ · MARY ·) ⊢[ el S ] ∅
JOHN_LOVES_MARY = ⇒ₑ ax (⇐ₑ ax ax)
john_loves_mary : Bool
john_loves_mary = [ JOHN_LOVES_MARY ] (john , (loves , (mary , ∅))) (id , ∅)

MARY_LOVES_EVERYONE : λC⁻ · MARY · ⊗ (· LOVES · ⊗ · EVERYONE₁ ·) ⊢[ el S ] ∅
MARY_LOVES_EVERYONE = ⇒ₑ ax (⇐ₑ ax (⊗ₑ [] ax (⇐ₑ ax ax)))
mary_loves_everyone : Bool
mary_loves_everyone = [ MARY_LOVES_EVERYONE ] (mary , (loves , (everyone₁ , ∅))) (id , ∅)

EVERYONE_LOVES_MARY : λC⁻ · EVERYONE₁ · ⊗ (· LOVES · ⊗ · MARY ·) ⊢[ el S ] ∅
EVERYONE_LOVES_MARY = ⊗ₑ ([] <⊗ _) ax (⇒ₑ (⇐ₑ ax ax) (⇐ₑ ax ax))
everyone_loves_mary : Bool
everyone_loves_mary = [ EVERYONE_LOVES_MARY ] (everyone₁ , (loves , (mary , ∅))) (id , ∅)


-- The order of application of what is the only rule that allows us
-- some leeway in when it should be applied (the product elimination)
-- does not seem to matter; whatever we do, we get the inverse scope
-- reading.

EVERYONE_LOVES_SOMEONE₁ : λC⁻ · EVERYONE₁ · ⊗ (· LOVES · ⊗ · SOMEONE₁ ·) ⊢[ el S ] ∅
EVERYONE_LOVES_SOMEONE₁ = ⇒ₑ (⊗ₑ [] ax (⇐ₑ ax ax)) (⇐ₑ ax (⊗ₑ [] ax (⇐ₑ ax ax)))
everyone_loves_someone₁ : Bool
everyone_loves_someone₁ = [ EVERYONE_LOVES_SOMEONE₁ ] (everyone₁ , (loves , (someone₁ , ∅))) (id , ∅)

-- Back to the drawing board!

EVERYONE_LOVES_SOMEONE₂ : λC⁻ · EVERYONE₁ · ⊗ (· LOVES · ⊗ · SOMEONE₁ ·) ⊢[ el S ] ∅
EVERYONE_LOVES_SOMEONE₂ = {!!}
everyone_loves_someone₂ : Bool
everyone_loves_someone₂ = [ EVERYONE_LOVES_SOMEONE₂ ] (everyone₁ , (loves , (someone₁ , ∅))) (id , ∅)
