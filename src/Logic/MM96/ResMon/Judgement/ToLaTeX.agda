--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Judgement/ToLaTeX.agda
--------------------------------------------------------------------------------


open import Data.String
open import Logic.ToLaTeX


module Logic.MM96.ResMon.Judgement.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.MM96.Type             Atom
open import Logic.MM96.Type.ToLaTeX     Atom
open import Logic.MM96.ResMon.Judgement Atom



instance
  JudgementToLaTeX : {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX Judgement
  JudgementToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : Judgement → String
      go (A ⊢ B) = toLaTeX A ++  " \\fCenter " ++ toLaTeX B
