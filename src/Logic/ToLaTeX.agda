------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function    using (_∘_)
open import Data.Bool   using (Bool; true; false)
open import Data.Fin    using (Fin; #_; suc; zero)
open import Data.Nat    using (ℕ)
open import Data.String using (String; unlines; _++_)
open import Data.List   using (List; _∷_; [_]; map; concat)


module Logic.ToLaTeX where


record ToLaTeX {ℓ} (A : Set ℓ) : Set ℓ where
  field
    toLaTeXPrec : ℕ → A → String

  toLaTeX : A → String
  toLaTeX = toLaTeXPrec 0


infixr 5 _∙_

_∙_ : String → String → String
x ∙ y = x ++ " " ++ y


parens : Bool → String → String
parens true  str = "(" ++ str ++ ")"
parens false str =        str


data BussProof : Set where
  AX : (rule judgement : String) → BussProof
  UI : (rule judgement : String) → BussProof → BussProof
  BI : (rule judgement : String) → BussProof → BussProof → BussProof
  TI : (rule judgement : String) → BussProof → BussProof → BussProof → BussProof


BussProofToLaTeX : ToLaTeX BussProof
BussProofToLaTeX = record { toLaTeXPrec = λ _ → proofTree }
  where
    lbl : String → String
    lbl r = "\\RightLabel{\\tiny{$(" ++ r ++ ")$}}"

    inf : Fin 4 → String → String
    inf zero                   j = "\\AXC{$" ++ j ++ "$}"
    inf (suc zero)             j = "\\UIC{$" ++ j ++ "$}"
    inf (suc (suc zero))       j = "\\BIC{$" ++ j ++ "$}"
    inf (suc (suc (suc zero))) j = "\\TIC{$" ++ j ++ "$}"
    inf (suc (suc (suc (suc ()))))

    go : BussProof → List String
    go (AX r j)       = concat (                     [ lbl r ∷ [ inf (# 0) j ] ])
    go (UI r j x)     = concat (go x ∷               [ lbl r ∷ [ inf (# 1) j ] ])
    go (BI r j x y)   = concat (go x ∷ go y ∷        [ lbl r ∷ [ inf (# 2) j ] ])
    go (TI r j x y z) = concat (go x ∷ go y ∷ go z ∷ [ lbl r ∷ [ inf (# 3) j ] ])

    proofTree : BussProof → String
    proofTree p = "\\begin{prooftree}%\n" ++ unlines (go p) ++ "\\end{prooftree}%"
