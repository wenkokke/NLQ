------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.String
open import Logic.ToLaTeX


module Logic.LG.Sequent.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.LG.Type                        Atom
open import Logic.LG.Type.ToLaTeX                Atom
open import Logic.LG.Structure.Polarised         Atom
open import Logic.LG.Structure.Polarised.ToLaTeX Atom
open import Logic.LG.Sequent                   Atom



instance
  SequentToLaTeX : {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX Sequent
  SequentToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : Sequent → String
      go (  X  ⊢  Y  ) =               toLaTeX X ++  " \\fCenter "         ++ toLaTeX Y
      go ([ A ]⊢  Y  ) = "\\focus{" ++ toLaTeX A ++ "} \\fCenter "         ++ toLaTeX Y
      go (  X  ⊢[ B ]) =               toLaTeX X ++ "  \\fCenter \\focus{" ++ toLaTeX B ++ "}"
