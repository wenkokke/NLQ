------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Product using (_×_; _,_)
open import Data.String


module Logic.Polarity.ToLaTeX {ℓ} (Univ : Set ℓ) where


open import Logic.ToLaTeX
open import Logic.Polarity


instance
  PolarisedUnivToLaTeX : {{UnivToLaTeX : ToLaTeX Univ}} → ToLaTeX (Polarity × Univ)
  PolarisedUnivToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}
      go : (Polarity × Univ) → String
      go (+ , A) = toLaTeX A ++ "^+"
      go (- , A) = toLaTeX A ++ "^-"
