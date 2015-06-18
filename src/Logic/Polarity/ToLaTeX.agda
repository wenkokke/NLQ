------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Product using (_×_; _,_)
open import Data.String


module Logic.Polarity.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.ToLaTeX
open import Logic.Polarity


instance
  PolarisedAtomToLaTeX : {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (Polarity × Atom)
  PolarisedAtomToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}
      go : (Polarity × Atom) → String
      go (+ , A) = toLaTeX A
      go (- , A) = toLaTeX A ++ "^-"
