------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.List     using (List) renaming ([] to ∅; _∷_ to _,_)
open import Data.String
open import Logic.ToLaTeX


module Logic.Intuitionistic.Unrestricted.Lambda.Judgement.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.Intuitionistic.Unrestricted.Lambda.Type         Atom
open import Logic.Intuitionistic.Unrestricted.Lambda.Type.ToLaTeX Atom
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement    Atom



instance
  ListTypeToLaTeX :  {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (List Type)
  ListTypeToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : List Type → String
      go      ∅  = ""
      go (A , Γ) = toLaTeX A ∙ "," ∙ go Γ


instance
  JudgementToLaTeX : {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX Judgement
  JudgementToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : Judgement → String
      go (Γ ⊢ A) = toLaTeX Γ ++ " \\fCenter " ++ toLaTeX A
