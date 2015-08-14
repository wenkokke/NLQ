--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/ToLaTeX.agda
--------------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.String
open import Logic.ToLaTeX


module Logic.MM96.ResMon.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.MM96.Type                     Atom
open import Logic.MM96.Type.ToLaTeX             Atom
open import Logic.MM96.ResMon.Judgement         Atom
open import Logic.MM96.ResMon.Judgement.ToLaTeX Atom
open import Logic.MM96.ResMon.Base              Atom


instance
  aMM96ToLaTeX : ∀ {J} {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (MM96 J)
  aMM96ToLaTeX = record { toLaTeXPrec = λ _ → B.toLaTeX ∘ bussProof }
    where
      module B = ToLaTeX BussProofToLaTeX
      module J = ToLaTeX JudgementToLaTeX

      mutual
        bussProof : ∀ {J} (f : MM96 J) → BussProof
        bussProof {J} f = bussProof′ f (J.toLaTeX J)

        bussProof′ : ∀ {J} (f : MM96 J) → (String → BussProof)
        bussProof′  ax        j = AX "\\text{ax}"               j
        bussProof′ (m⟨t⟩  )   j = AX "m\\langle t \\rangle"     j
        bussProof′ (m⟨l⟩ f)   j = UI "m\\langle l \\rangle"     j (bussProof f)
        bussProof′ (m⟨r⟩ f)   j = UI "m\\langle r \\rangle"     j (bussProof f)
        bussProof′ (m□   f)   j = UI "m\\varbox"                j (bussProof f)
        bussProof′ (m◇   f)   j = UI "m\\vardia"                j (bussProof f)
        bussProof′ (r□◇  f)   j = UI "r\\varbox\\vardia"        j (bussProof f)
        bussProof′ (r◇□  f)   j = UI "r\\vardia\\varbox"        j (bussProof f)
        bussProof′ (m⊗   f g) j = BI "m\\varotimes"             j (bussProof f) (bussProof g)
        bussProof′ (m⇒   f g) j = BI "m\\varbslash"             j (bussProof f) (bussProof g)
        bussProof′ (m⇐   f g) j = BI "m\\varslash"              j (bussProof f) (bussProof g)
        bussProof′ (r⇒⊗  f)   j = UI "r\\varbslash\\varotimes"  j (bussProof f)
        bussProof′ (r⊗⇒  f)   j = UI "r\\varotimes\\varbslash"  j (bussProof f)
        bussProof′ (r⇐⊗  f)   j = UI "r\\varslash\\varotimes"   j (bussProof f)
        bussProof′ (r⊗⇐  f)   j = UI "r\\varotimes\\varslash"   j (bussProof f)
        bussProof′ (m⊙   f g) j = BI "m\\varoplus"              j (bussProof f) (bussProof g)
        bussProof′ (m⇨   f g) j = BI "m\\varobslash"            j (bussProof f) (bussProof g)
        bussProof′ (m⇦   f g) j = BI "m\\varoslash"             j (bussProof f) (bussProof g)
        bussProof′ (r⇨⊙  f)   j = UI "r\\varobslash\\varoplus"  j (bussProof f)
        bussProof′ (r⊙⇨  f)   j = UI "r\\varoplus\\varobslash"  j (bussProof f)
        bussProof′ (r⊙⇦  f)   j = UI "r\\varoplus\\varoslash"   j (bussProof f)
        bussProof′ (r⇦⊙  f)   j = UI "r\\varoslash\\varoplus"   j (bussProof f)
        bussProof′ (p₀   f)   j = UI "p_{0}"                    j (bussProof f)
        bussProof′ (p₀′  f)   j = UI "p_{0}\\prime"             j (bussProof f)
        bussProof′ (p₁   f)   j = UI "p_{1}"                    j (bussProof f)
        bussProof′ (p₁′  f)   j = UI "p_{1}\\prime"             j (bussProof f)
        bussProof′ (p₂   f)   j = UI "p_{2}"                    j (bussProof f)
        bussProof′ (p₂′  f)   j = UI "p_{2}\\prime"             j (bussProof f)
