------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Data.Fin                              using (Fin; #_)
open import Data.List                             using (List; map; _++_) renaming ([] to ∅; _∷_ to _,_)
open import Data.List.Properties                  using (map-++-commute)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)


module TypeAndEffect.Classical.Unrestricted.LambdaCMinus.ToLogic {ℓ} (Univ : Set ℓ) where


open import Logic.Translation
open import TypeAndEffect.Type                                     Univ as TET
open import TypeAndEffect.Judgement                                Univ as TEJ
open import TypeAndEffect.Classical.Unrestricted.LambdaCMinus.Base Univ as TEB
open import Logic.Classical.Linear.LambdaCMinus.Type Univ as LOT
open import Logic.Classical.Linear.LambdaCMinus.Judgement Univ as LOJ
open import Logic.Classical.Unrestricted.LambdaCMinus.Base         Univ as LOB


private
  ⟦_⟧ᵀ : TET.Type → LOT.Type
  ⟦ el A             ⟧ᵀ = el A
  ⟦  ¬ A ^ U         ⟧ᵀ = ⟦ A ⟧ᵀ - ⟦ U ⟧ᵀ
  ⟦    A ^ U ⇒ B ^ T ⟧ᵀ = ⟦ A ⟧ᵀ - ⟦ T ⟧ᵀ ⇒ ⟦ B ⟧ᵀ - ⟦ U ⟧ᵀ
  ⟦_⟧ᴸ : List TET.Type → List LOT.Type
  ⟦_⟧ᴸ = map ⟦_⟧ᵀ

  ⟦_⟧ᴶ : TEJ.Judgement → LOJ.Judgement
  ⟦ Γ     ⊢          Δ ^ T ⟧ᴶ = ⟦ Γ ⟧ᴸ ⊢                    ⟦ T ⟧ᵀ , ⟦ Δ ⟧ᴸ
  ⟦ Γ ^ U ⊢[ A ^ T ] Δ     ⟧ᴶ = ⟦ Γ ⟧ᴸ ⊢[ ⟦ A ⟧ᵀ - ⟦ U ⟧ᵀ ] ⟦ T ⟧ᵀ , ⟦ Δ ⟧ᴸ

  [_] : ∀ {J} → TEB.λC⁻ J → LOB.λC⁻ ⟦ J ⟧ᴶ
  [ ax                 ] = -ᵢ ax (⇒ₑᵏ (# 0) (axᵢ (# 0)))
  [ ⇒ᵢ             f   ] = ∅ₑ (-ᵢ (⇒ᵢ (-ₑ ax (eᴿ₁ (wᴿ₁ [ f ])))) (⇒ₑᵏ (# 0) ax))
  [ ⇒ₑ   {Γ₁} {Γ₂} f x ] rewrite map-++-commute ⟦_⟧ᵀ Γ₁ Γ₂ = -ₑ [ f ] (⇒ₑ ax (eᴿ₁ (wᴿ₁ [ x ])))
  [ raa            f   ] = raa (eᴿ₁′ [ f ])
  [ raaᵀ           f   ] = ∅ₑ (-ᵢ (raa (eᴿ₁′ (wᴿ₁′ [ f ]))) (⇒ₑᵏ (# 0) ax))
  [ ⇒ₑᵏ            f   ] = ⇒ₑᵏ (# 1) [ f ]
  [ ⇒ₑᵏᵀ           f   ] = ⇒ₑᵏ (# 0) (∅ₑ (-ₑ [ f ] (raa (⇒ₑᵏ (# 1) (eᴿ₁ ax)))))
