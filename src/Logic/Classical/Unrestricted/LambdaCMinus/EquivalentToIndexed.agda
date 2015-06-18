------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Algebra                               using (module Monoid)
open import Function                              using (id; _∘_)
open import Function.Equivalence                  using (_⇔_; equivalence)
open import Data.Fin                              using (Fin; suc; zero; #_)
open import Data.List                             using (List; _∷_; [];_++_)
open import Data.Product                          using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; map)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable            using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)


module Logic.Classical.Unrestricted.LambdaCMinus.EquivalentToIndexed {ℓ} (Atom : Set ℓ) where


open import Logic.Index
open import Logic.Translation
open import Logic.Classical.Unrestricted.LambdaCMinus.Type         Atom
open import Logic.Classical.Unrestricted.LambdaCMinus.Judgement    Atom
open import Logic.Classical.Unrestricted.LambdaCMinus.Base         Atom as E
open import Logic.Classical.Unrestricted.LambdaCMinus.Indexed.Base Atom as I
open Monoid (Data.List.monoid Type) using (identity; assoc)


from : ∀ {J} → E.λC⁻ J → I.λC⁻ J
from (ax                 ) = I.ax    (# 0)
from (⇒ᵢ              f  ) = I.⇒ᵢ    (from f)
from (⇒ₑ  {Γ₁} {Γ₂}   f g) = I.⇒ₑ    (I.sᴸ Γ₁ (I.wᴸ Γ₂ (from f))) (I.wᴸ Γ₁ (from g))
from (raa             f  ) = I.raa   (from f)
from (⇒ₑᵏ             α f) = I.⇒ₑᵏ α (from f)
from (-ᵢ  {Γ₁} {Γ₂}   f g) = I.-ᵢ    (I.sᴸ Γ₁ (I.wᴸ Γ₂ (from f))) (I.eᴸ′ [] (_ ∷ []) Γ₁ Γ₂ (I.wᴸ′ Γ₁ (from g)))
from (-ₑ  {Γ₁} {Γ₂}   f g) = I.-ₑ    (I.sᴸ Γ₁ (I.wᴸ Γ₂ (from f))) (I.eᴸ  [] (_ ∷ []) Γ₁ Γ₂ (I.wᴸ  Γ₁ (from g)))
from (⊗ᵢ  {Γ₁} {Γ₂}   f g) = I.⊗ᵢ    (I.sᴸ Γ₁ (I.wᴸ Γ₂ (from f))) (I.wᴸ  Γ₁ (from g))
from (⊗ₑ  {Γ₁} {Γ₂}   f g) = I.⊗ₑ    (I.sᴸ Γ₁ (I.wᴸ Γ₂ (from f))) (I.eᴸ  [] (_ ∷ (_ ∷ [])) Γ₁ Γ₂ (I.wᴸ Γ₁ (from g)))
from (eᴸ  Γ₁ Γ₂ Γ₃ Γ₄ f  ) = I.eᴸ    Γ₁ Γ₂ Γ₃ Γ₄ (from f)
from (cᴸ₁             f  ) = I.cᴸ₁   (from f)
from (wᴸ₁             f  ) = I.wᴸ₁   (from f)


private
  lem-cᴸ-[] : ∀ {Γ A Δ} → E.λC⁻ Γ ++ Γ ⊢[ A ] Δ → E.λC⁻ Γ ⊢[ A ] Δ
  lem-cᴸ-[] {Γ} = subst (λ Γ′ → E.λC⁻ Γ ++ Γ′ ⊢[ _ ] _ → E.λC⁻ Γ′ ⊢[ _ ] _) (proj₂ identity Γ) (E.cᴸ Γ [])


to : ∀ {J} → I.λC⁻ J → E.λC⁻ J
to (I.ax  x   ) = E.axᵢ x
to (I.⇒ᵢ  f   ) = E.⇒ᵢ (to f)
to (I.⇒ₑ  f g ) = lem-cᴸ-[] (E.⇒ₑ (to f) (to g))
to (I.raa f   ) = E.raa (to f)
to (I.⇒ₑᵏ α f ) = E.⇒ₑᵏ α (to f)
to (I.-ᵢ  f g ) = lem-cᴸ-[] (E.-ᵢ (to f) (to g))
to (I.-ₑ  f g ) = lem-cᴸ-[] (E.-ₑ (to f) (to g))
to (I.⊗ᵢ  f g ) = lem-cᴸ-[] (E.⊗ᵢ (to f) (to g))
to (I.⊗ₑ  f g ) = lem-cᴸ-[] (E.⊗ₑ (to f) (to g))


eq : ∀ {J} → (E.λC⁻ J) ⇔ (I.λC⁻ J)
eq = equivalence from to


Un→Ix : Translation Type Type E.λC⁻_ I.λC⁻_
Un→Ix = record { ⟦_⟧ᵀ = id ; ⟦_⟧ᴶ = id ; [_] = from }

Ix→Un : Translation Type Type I.λC⁻_ E.λC⁻_
Ix→Un = record { ⟦_⟧ᵀ = id ; ⟦_⟧ᴶ = id ; [_] = to }
