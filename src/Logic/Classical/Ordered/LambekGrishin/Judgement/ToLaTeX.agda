------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.String
open import Logic.ToLaTeX


module Logic.Classical.Ordered.LambekGrishin.Judgement.ToLaTeX {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type                        Univ
open import Logic.Classical.Ordered.LambekGrishin.Type.ToLaTeX                Univ
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised         Univ
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised.ToLaTeX Univ
open import Logic.Classical.Ordered.LambekGrishin.Judgement                   Univ



instance
  JudgementToLaTeX : {{UnivToLaTeX : ToLaTeX Univ}} → ToLaTeX Judgement
  JudgementToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : Judgement → String
      go (  X  ⊢  Y  ) =               toLaTeX X ++  " \\fCenter "         ++ toLaTeX Y
      go ([ A ]⊢  Y  ) = "\\focus{" ++ toLaTeX A ++ "} \\fCenter "         ++ toLaTeX Y
      go (  X  ⊢[ B ]) =               toLaTeX X ++ "  \\fCenter \\focus{" ++ toLaTeX B ++ "}"
