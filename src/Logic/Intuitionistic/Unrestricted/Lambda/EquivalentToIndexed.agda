------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra                               using (module Monoid)
open import Function                              using (id)
open import Function.Equivalence                  using (_⇔_; equivalence)
open import Data.Fin                              using (Fin; suc; zero; #_)
open import Data.List                             using (List; _++_) renaming ([] to ∅; _∷_ to _,_)
open import Data.Product                          using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)


module Logic.Intuitionistic.Unrestricted.Lambda.EquivalentToIndexed {ℓ} (Univ : Set ℓ) where


open import Logic.Index
open import Logic.Translation
open import Logic.Intuitionistic.Unrestricted.Lambda.Type         Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement    Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Base         Univ as E
open import Logic.Intuitionistic.Unrestricted.Lambda.Indexed.Base Univ as I
open Monoid (Data.List.monoid Type) using (identity; assoc)


from : ∀ {J} → E.Λ J → I.Λ J
from  ax                   = ax (# 0)
from (⇒ᵢ              f)   = ⇒ᵢ (from f)
from (⇒ₑ  {Γ₁} {Γ₂}   f g) = ⇒ₑ (sᴸ′ Γ₁ (wᴸ′ Γ₂ (from f))) (wᴸ′ Γ₁ (from g))
from (⊗ᵢ  {Γ₁} {Γ₂}   f g) = ⊗ᵢ (sᴸ′ Γ₁ (wᴸ′ Γ₂ (from f))) (wᴸ′ Γ₁ (from g))
from (⊗ₑ  {Γ₁} {Γ₂}   f g) = ⊗ₑ (sᴸ′ Γ₁ (wᴸ′ Γ₂ (from f))) (eᴸ′ ∅ (_ , (_ , ∅)) Γ₁ Γ₂ (wᴸ′ Γ₁ (from g)))
from (wᴸ₁             f)   = wᴸ₁′            (from f)
from (cᴸ₁             f)   = cᴸ₁′            (from f)
from (eᴸ Γ₁ Γ₂ Γ₃ Γ₄  f)   = eᴸ′ Γ₁ Γ₂ Γ₃ Γ₄ (from f)


private
  lem-ax : ∀ {Γ} (x : Fin _) → E.Λ Γ ⊢ Γ ‼ x
  lem-ax {∅} ()
  lem-ax {A , Γ}  zero   = E.sᴸ (A , ∅) (E.wᴸ Γ ax)
  lem-ax {_ , Γ} (suc x) = wᴸ₁ (lem-ax x)

  lem-cᴸ-∅ : ∀ {Γ A} → E.Λ Γ ++ Γ ⊢ A → E.Λ Γ ⊢ A
  lem-cᴸ-∅ {Γ} = subst (λ Γ′ → E.Λ Γ ++ Γ′ ⊢ _ → E.Λ Γ′ ⊢ _) (proj₂ identity Γ) (cᴸ Γ ∅)


to : ∀ {J} → I.Λ J → E.Λ J
to (ax x)   = lem-ax x
to (⇒ᵢ f)   = ⇒ᵢ (to f)
to (⇒ₑ f g) = lem-cᴸ-∅ (⇒ₑ (to f) (to g))
to (⊗ᵢ f g) = lem-cᴸ-∅ (⊗ᵢ (to f) (to g))
to (⊗ₑ f g) = lem-cᴸ-∅ (⊗ₑ (to f) (to g))


eq : ∀ {J} → (E.Λ J) ⇔ (I.Λ J)
eq = equivalence from to

Un→Ix : Translation Type Type E.Λ_ I.Λ_
Un→Ix = record { ⟦_⟧ᵀ = id ; ⟦_⟧ᴶ = id ; [_] = from }

Ix→Un : Translation Type Type I.Λ_ E.Λ_
Ix→Un = record { ⟦_⟧ᵀ = id ; ⟦_⟧ᴶ = id ; [_] = to }
