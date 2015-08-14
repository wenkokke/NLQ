------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function     using (_∘_)
open import Data.Product using (_×_; _,_)
open import Data.String

open import Logic.Polarity



module Logic.LG.Pol.ToLaTeX
  {ℓ} (Atom : Set ℓ) (Polarityᴬ? : Atom → Polarity) where


open import Logic.ToLaTeX
open import Logic.Polarity.ToLaTeX      Atom
open import Logic.LG.Pol.Base        Atom Polarityᴬ?
open import Logic.LG.ToLaTeX            Atom
open import Logic.LG.EquivalentToPol Atom Polarityᴬ?


instance
  fLGToLaTeX : ∀ {J} {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (fLG J)
  fLGToLaTeX = record { toLaTeXPrec = λ _ f → toLaTeX (from f) }
    where
      open ToLaTeX {{...}}
