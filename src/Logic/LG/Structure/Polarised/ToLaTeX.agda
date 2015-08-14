------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.String
open import Logic.ToLaTeX


module Logic.LG.Structure.Polarised.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.LG.Structure.Polarised Atom
open import Logic.LG.Structure.ToLaTeX   Atom


instance
  PolarisedStructureToLaTeX : ∀ {p} {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (Structure p)
  PolarisedStructureToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX ∘ forget }
    where
      open ToLaTeX {{...}}
      open Correct using (forget)
