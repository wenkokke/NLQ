------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function  using (id)
open import Data.List using (List; map; _++_) renaming ([] to ∅; _∷_ to _,_)


module Logic.Intuitionistic.Linear.Lambda.ToUnrestricted {ℓ} (Univ : Set ℓ) where


open import Logic.Index
open import Logic.Translation
open import Logic.Intuitionistic.Linear.Lambda.Base            Univ as L
open import Logic.Intuitionistic.Unrestricted.Lambda.Type      Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Base      Univ as U


private
  [_] : ∀ {J} → L.Λ J → U.Λ J
  [ L.ax                  ] = U.ax
  [ L.⇒ᵢ              f   ] = U.⇒ᵢ    [ f ]
  [ L.⇒ₑ              f g ] = U.⇒ₑ    [ f ] [ g ]
  [ L.⊗ᵢ              f g ] = U.⊗ᵢ    [ f ] [ g ]
  [ L.⊗ₑ              f g ] = U.⊗ₑ    [ f ] [ g ]
  [ L.eᴸ  Γ₁ Γ₂ Γ₃ Γ₄ f   ] = U.eᴸ  Γ₁ Γ₂ Γ₃ Γ₄ [ f ]


LL→Λ : Translation Type Type L.Λ_ U.Λ_
LL→Λ = record { ⟦_⟧ᵀ = id ; ⟦_⟧ᴶ = id ; [_] = [_] }
