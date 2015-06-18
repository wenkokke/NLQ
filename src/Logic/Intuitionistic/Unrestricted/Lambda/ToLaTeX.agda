------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.String
open import Logic.ToLaTeX


module Logic.Intuitionistic.Unrestricted.Lambda.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.Intuitionistic.Unrestricted.Lambda.Type                        Atom
open import Logic.Intuitionistic.Unrestricted.Lambda.Type.ToLaTeX                Atom
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement                   Atom
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement.ToLaTeX           Atom
open import Logic.Intuitionistic.Unrestricted.Lambda.Base                        Atom

instance
  LambdaToLaTeX : ∀ {J} {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (Λ J)
  LambdaToLaTeX = record { toLaTeXPrec = λ _ → B.toLaTeX ∘ bussProof }
    where
      module B = ToLaTeX BussProofToLaTeX
      module J = ToLaTeX JudgementToLaTeX

      mutual
        bussProof : ∀ {J} (f : Λ J) → BussProof
        bussProof {J} f = bussProof′ f (J.toLaTeX J)

        bussProof′ : ∀ {J} (f : Λ J) → (String → BussProof)
        bussProof′  ax               j = AX "\\text{ax}"     j
        bussProof′ (⇒ᵢ          f)   j = UI "\\RightArrow_i" j (bussProof f)
        bussProof′ (⇒ₑ          f g) j = BI "\\RightArrow_e" j (bussProof f) (bussProof g)
        bussProof′ (⊗ᵢ          f g) j = BI "\\times_i"      j (bussProof f) (bussProof g)
        bussProof′ (⊗ₑ          f g) j = BI "\\times_e"      j (bussProof f) (bussProof g)
        bussProof′ (wᴸ₁         f)   j = UI "w"              j (bussProof f)
        bussProof′ (cᴸ₁         f)   j = UI "c"              j (bussProof f)
        bussProof′ (eᴸ _ _ _ _  f)   j = bussProof f
