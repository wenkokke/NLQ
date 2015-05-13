------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.List     using (List) renaming ([] to ∅; _∷_ to _,_)
open import Data.String
open import Logic.ToLaTeX


module Logic.Intuitionistic.Unrestricted.Lambda.Judgement.ToLaTeX {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Unrestricted.Lambda.Type         Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Type.ToLaTeX Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement    Univ



instance
  ListTypeToLaTeX :  {{UnivToLaTeX : ToLaTeX Univ}} → ToLaTeX (List Type)
  ListTypeToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : List Type → String
      go      ∅  = ""
      go (A , Γ) = toLaTeX A ∙ "," ∙ go Γ


instance
  JudgementToLaTeX : {{UnivToLaTeX : ToLaTeX Univ}} → ToLaTeX Judgement
  JudgementToLaTeX = record { toLaTeXPrec = λ _ → go }
    where
      open ToLaTeX {{...}}

      go : Judgement → String
      go (Γ ⊢ A) = toLaTeX Γ ++ " \\fCenter " ++ toLaTeX A
