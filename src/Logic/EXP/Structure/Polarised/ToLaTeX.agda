--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/Structure/Polarised/ToLaTeX.agda
--------------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.String
open import Logic.ToLaTeX


module Logic.EXP.Structure.Polarised.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.EXP.Structure.Polarised Atom
open import Logic.EXP.Structure.ToLaTeX   Atom


instance
  PolarisedStructureToLaTeX : ∀ {p} {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (Structure p)
  PolarisedStructureToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX ∘ forget }
    where
      open ToLaTeX {{...}}
      open Correct using (forget)
