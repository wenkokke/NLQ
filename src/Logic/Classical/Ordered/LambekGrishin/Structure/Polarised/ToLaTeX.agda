------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.String
open import Logic.ToLaTeX


module Logic.Classical.Ordered.LambekGrishin.Structure.Polarised.ToLaTeX {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Univ
open import Logic.Classical.Ordered.LambekGrishin.Structure.ToLaTeX   Univ


instance
  PolarisedStructureToLaTeX : ∀ {p} {{UnivToLaTeX : ToLaTeX Univ}} → ToLaTeX (Structure p)
  PolarisedStructureToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX ∘ forget }
    where
      open ToLaTeX {{...}}
      open Correct using (forget)
