------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.String
open import Logic.ToLaTeX


module Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type             Atom
open import Logic.Classical.Ordered.LambekGrishin.Type.ToLaTeX     Atom
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement Atom



instance
  JudgementToLaTeX : {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX Judgement
  JudgementToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : Judgement → String
      go (A ⊢ B) = toLaTeX A ++  " \\fCenter " ++ toLaTeX B
