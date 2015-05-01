------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function     using (_∘_)
open import Data.Product using (_×_; _,_)
open import Data.String



module Logic.Classical.Ordered.LambekGrishin.FocPol.ToLaTeX {ℓ} (Univ : Set ℓ) where


open import Logic.ToLaTeX
open import Logic.Polarity
open import Logic.Polarity.ToLaTeX                                   Univ
open import Logic.Classical.Ordered.LambekGrishin.FocPol.Base        Univ
open import Logic.Classical.Ordered.LambekGrishin.ToLaTeX            (Polarity × Univ)
open import Logic.Classical.Ordered.LambekGrishin.EquivalentToFocPol Univ


instance
  PolarisedLambekGrishinToLaTeX : ∀ {J} {{UnivToLaTeX : ToLaTeX Univ}} → ToLaTeX (LG J)
  PolarisedLambekGrishinToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX ∘ from }
    where
      open ToLaTeX {{...}}
