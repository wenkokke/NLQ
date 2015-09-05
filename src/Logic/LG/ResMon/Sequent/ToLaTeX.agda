------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.String
open import Logic.ToLaTeX


module Logic.LG.ResMon.Sequent.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.LG.Type             Atom
open import Logic.LG.Type.ToLaTeX     Atom
open import Logic.LG.ResMon.Sequent Atom



instance
  SequentToLaTeX : {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX Sequent
  SequentToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : Sequent → String
      go (A ⊢ B) = toLaTeX A ++  " \\fCenter " ++ toLaTeX B
