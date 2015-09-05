--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Sequent/ToLaTeX.agda
--------------------------------------------------------------------------------


open import Data.String
open import Logic.ToLaTeX


module Logic.MM96.ResMon.Sequent.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.MM96.Type             Atom
open import Logic.MM96.Type.ToLaTeX     Atom
open import Logic.MM96.ResMon.Sequent Atom



instance
  SequentToLaTeX : {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX Sequent
  SequentToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : Sequent → String
      go (A ⊢ B) = toLaTeX A ++  " \\fCenter " ++ toLaTeX B
