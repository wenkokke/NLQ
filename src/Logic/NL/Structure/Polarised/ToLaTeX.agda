--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/Structure/Polarised/ToLaTeX.agda
--------------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.String
open import Logic.ToLaTeX


module Logic.NL.Structure.Polarised.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Structure.Polarised Atom
open import Logic.NL.Structure.ToLaTeX   Atom


instance
  PolarisedStructureToLaTeX : ∀ {p} {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (Structure p)
  PolarisedStructureToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX ∘ forget }
    where
      open ToLaTeX {{...}}
      open Correct using (forget)
