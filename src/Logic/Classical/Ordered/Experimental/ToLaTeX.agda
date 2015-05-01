------------------------------------------------------------------------
-- The Lambek Calculus in Agda
-- This file was automatically generated.
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.String
open import Logic.ToLaTeX


module Logic.Classical.Ordered.Experimental.ToLaTeX {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.Experimental.Type                        Univ
open import Logic.Classical.Ordered.Experimental.Type.ToLaTeX                Univ
open import Logic.Classical.Ordered.Experimental.Structure.Polarised         Univ
open import Logic.Classical.Ordered.Experimental.Structure.Polarised.ToLaTeX Univ
open import Logic.Classical.Ordered.Experimental.Judgement                   Univ
open import Logic.Classical.Ordered.Experimental.Judgement.ToLaTeX           Univ
open import Logic.Classical.Ordered.Experimental.Base                        Univ


instance
  ExperimentalToLaTeX : ∀ {J} {{UnivToLaTeX : ToLaTeX Univ}} → ToLaTeX (EXP J)
  ExperimentalToLaTeX = record { toLaTeXPrec = λ _ → B.toLaTeX ∘ bussProof }
    where
      module B = ToLaTeX BussProofToLaTeX
      module J = ToLaTeX JudgementToLaTeX

      mutual
        bussProof : ∀ {J} (f : EXP J) → BussProof
        bussProof {J} f = bussProof′ f (J.toLaTeX J)

        bussProof′ : ∀ {J} (f : EXP J) → (String → BussProof)
        bussProof′  ax⁺      j = AX "\\text{ax}^+"             j
        bussProof′  ax⁻      j = AX "\\text{ax}^-"             j
        bussProof′ (⇁   f)   j = UI "\\rightharpoondown"       j (bussProof f)
        bussProof′ (↽   f)   j = UI "\\leftharpoondown"        j (bussProof f)
        bussProof′ (⇀   f)   j = UI "\\rightharpoonup"         j (bussProof f)
        bussProof′ (↼   f)   j = UI "\\leftharpoonup"          j (bussProof f)
        bussProof′ (◇ᴸ  f)   j = UI "\\vardia L"               j (bussProof f)
        bussProof′ (◇ᴿ  f)   j = UI "\\vardia R"               j (bussProof f)
        bussProof′ (□ᴸ  f)   j = UI "\\varbox L"               j (bussProof f)
        bussProof′ (□ᴿ  f)   j = UI "\\varbox R"               j (bussProof f)
        bussProof′ (⊗ᴸ  f)   j = UI "\\varotimes L"            j (bussProof f)
        bussProof′ (⊗ᴿ  f g) j = BI "\\varotimes R"            j (bussProof f) (bussProof g)
        bussProof′ (⇒ᴸ  f g) j = BI "\\varbslash L"            j (bussProof f) (bussProof g)
        bussProof′ (⇒ᴿ  f)   j = UI "\\varbslash R"            j (bussProof f)
        bussProof′ (⇐ᴸ  f g) j = BI "\\varslash L"             j (bussProof f) (bussProof g)
        bussProof′ (⇐ᴿ  f)   j = UI "\\varslash R"             j (bussProof f)
        bussProof′ (r⇒⊗ f)   j = UI "r\\varbslash\\varotimes"  j (bussProof f)
        bussProof′ (r⊗⇒ f)   j = UI "r\\varotimes\\varbslash"  j (bussProof f)
        bussProof′ (r⇐⊗ f)   j = UI "r\\varslash\\varotimes"   j (bussProof f)
        bussProof′ (r⊗⇐ f)   j = UI "r\\varotimes\\varslash"   j (bussProof f)
        bussProof′ (⊕ᴸ  f g) j = BI "\\varoplus L"             j (bussProof f) (bussProof g)
        bussProof′ (⊕ᴿ  f)   j = UI "\\varoplus R"             j (bussProof f)
        bussProof′ (⇚ᴸ  f)   j = UI "\\varoslash L"            j (bussProof f)
        bussProof′ (⇚ᴿ  f g) j = BI "\\varoslash R"            j (bussProof f) (bussProof g)
        bussProof′ (⇛ᴸ  f)   j = UI "\\varobslash L"           j (bussProof f)
        bussProof′ (⇛ᴿ  f g) j = BI "\\varobslash R"           j (bussProof f) (bussProof g)
        bussProof′ (r⇚⊕ f)   j = UI "r\\varoslash\\varoplus"   j (bussProof f)
        bussProof′ (r⊕⇚ f)   j = UI "r\\varoplus\\varoslash"   j (bussProof f)
        bussProof′ (r⇛⊕ f)   j = UI "r\\varobslash\\varoplus"  j (bussProof f)
        bussProof′ (r⊕⇛ f)   j = UI "r\\varoplus\\varobslash"  j (bussProof f)
        bussProof′ (d⇛⇐ f)   j = UI "d\\varobslash\\varslash"  j (bussProof f)
        bussProof′ (d⇛⇒ f)   j = UI "d\\varobslash\\varbslash" j (bussProof f)
        bussProof′ (d⇚⇒ f)   j = UI "d\\varoslash\\varbslash"  j (bussProof f)
        bussProof′ (d⇚⇐ f)   j = UI "d\\varoslash\\varslash"   j (bussProof f)
