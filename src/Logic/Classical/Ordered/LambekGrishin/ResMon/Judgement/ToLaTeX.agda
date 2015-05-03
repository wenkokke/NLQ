------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.String
open import Logic.ToLaTeX


module Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement.ToLaTeX {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type             Univ
open import Logic.Classical.Ordered.LambekGrishin.Type.ToLaTeX     Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement Univ



instance
  JudgementToLaTeX : {{UnivToLaTeX : ToLaTeX Univ}} → ToLaTeX Judgement
  JudgementToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : Judgement → String
      go (A ⊢ B) = toLaTeX A ++  " \\fCenter " ++ toLaTeX B
