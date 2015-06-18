------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.String
open import Logic.ToLaTeX


module Logic.Classical.Ordered.LambekGrishin.Structure.Polarised.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Atom
open import Logic.Classical.Ordered.LambekGrishin.Structure.ToLaTeX   Atom


instance
  PolarisedStructureToLaTeX : ∀ {p} {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (Structure p)
  PolarisedStructureToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX ∘ forget }
    where
      open ToLaTeX {{...}}
      open Correct using (forget)
