------------------------------------------------------------------------
-- The Lambek Calculus in Agda
-- This file was automatically generated.
------------------------------------------------------------------------


open import Data.String
open import Logic.ToLaTeX


module Logic.Classical.Ordered.Experimental.Judgement.ToLaTeX {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.Experimental.Type                        Univ
open import Logic.Classical.Ordered.Experimental.Type.ToLaTeX                Univ
open import Logic.Classical.Ordered.Experimental.Structure.Polarised         Univ
open import Logic.Classical.Ordered.Experimental.Structure.Polarised.ToLaTeX Univ
open import Logic.Classical.Ordered.Experimental.Judgement                   Univ



instance
  JudgementToLaTeX : {{UnivToLaTeX : ToLaTeX Univ}} → ToLaTeX Judgement
  JudgementToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : Judgement → String
      go (  X  ⊢  Y  ) =               toLaTeX X ++  " \\fCenter "         ++ toLaTeX Y
      go ([ A ]⊢  Y  ) = "\\focus{" ++ toLaTeX A ++ "} \\fCenter "         ++ toLaTeX Y
      go (  X  ⊢[ B ]) =               toLaTeX X ++ "  \\fCenter \\focus{" ++ toLaTeX B ++ "}"
