open import Level     using (Level; suc; _⊔_)
open import Function  using (id)
open import Data.List using (List; _++_) renaming ([] to ·; _∷_ to _,_)


module Logic.Classical.Linear.LambdaCMinus.ToUnrestricted {ℓ} (Univ : Set ℓ) where


open import Logic.Type Univ renaming (_⇚_ to _-_)
open import Logic.Index renaming (lookup to _‼_)
open import Logic.Translation Univ 
open import Logic.Classical.Judgement (List Type) Type (List Type)
open import Logic.Classical.Linear.LambdaCMinus.Base Univ as L
open import Logic.Classical.Unrestricted.LambdaCMinus.Base Univ as U


private
  [_] : ∀ {J} → L.λC⁻ J → U.λC⁻ J
  [ L.ax                  ] = U.ax
  [ L.⇒ᵢ              f   ] = U.⇒ᵢ    [ f ]
  [ L.⇒ₑ              f g ] = U.⇒ₑ    [ f ] [ g ]
  [ L.raa             f   ] = U.raa   [ f ]
  [ L.⇒ₑᵏ             α f ] = U.⇒ₑᵏ α [ f ]
  [ L.-ᵢ              f g ] = U.-ᵢ    [ f ] [ g ]
  [ L.-ₑ              f g ] = U.-ₑ    [ f ] [ g ]
  [ L.⊗ᵢ              f g ] = U.⊗ᵢ    [ f ] [ g ]
  [ L.⊗ₑ              f g ] = U.⊗ₑ    [ f ] [ g ]
  [ L.eᴸ  Γ₁ Γ₂ Γ₃ Γ₄ f   ] = U.eᴸ  Γ₁ Γ₂ Γ₃ Γ₄ [ f ]


Lin→Un : Translation Type L.λC⁻_ U.λC⁻_
Lin→Un = record { ⟦_⟧ᵀ = id ; ⟦_⟧ᴶ = id ; [_] = [_] }
