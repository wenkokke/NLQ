------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.String
open import Logic.ToLaTeX


module Logic.LG.ResMon.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.LG.Type                     Atom
open import Logic.LG.Type.ToLaTeX             Atom
open import Logic.LG.ResMon.Sequent         Atom
open import Logic.LG.ResMon.Sequent.ToLaTeX Atom
open import Logic.LG.ResMon.Base              Atom


instance
  aLGToLaTeX : ∀ {J} {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (LG J)
  aLGToLaTeX = record { toLaTeXPrec = λ _ → B.toLaTeX ∘ bussProof }
    where
      module B = ToLaTeX BussProofToLaTeX
      module J = ToLaTeX SequentToLaTeX

      mutual
        bussProof : ∀ {J} (f : LG J) → BussProof
        bussProof {J} f = bussProof′ f (J.toLaTeX J)

        bussProof′ : ∀ {J} (f : LG J) → (String → BussProof)
        bussProof′  ax        j = AX "\\text{ax}"               j
        bussProof′ (m□   f)   j = UI "m\\varbox"                j (bussProof f)
        bussProof′ (m◇   f)   j = UI "m\\vardia"                j (bussProof f)
        bussProof′ (r□◇  f)   j = UI "r\\varbox\\vardia"        j (bussProof f)
        bussProof′ (r◇□  f)   j = UI "r\\vardia\\varbox"        j (bussProof f)
        bussProof′ (m⁰   f)   j = UI "m\\varsuff0"              j (bussProof f)
        bussProof′ (m₀   f)   j = UI "m\\varpref0"              j (bussProof f)
        bussProof′ (r⁰₀  f)   j = UI "r\\varsuff0\\varpref0"    j (bussProof f)
        bussProof′ (r₀⁰  f)   j = UI "r\\varpref0\\varsuff0"    j (bussProof f)
        bussProof′ (m₁   f)   j = UI "m\\varpref1"              j (bussProof f)
        bussProof′ (m¹   f)   j = UI "m\\varsuff1"              j (bussProof f)
        bussProof′ (r¹₁  f)   j = UI "r\\varsuff1\\varpref1"    j (bussProof f)
        bussProof′ (r₁¹  f)   j = UI "r\\varpref1\\varsuff1"    j (bussProof f)
        bussProof′ (m⊗   f g) j = BI "m\\varotimes"             j (bussProof f) (bussProof g)
        bussProof′ (m⇒   f g) j = BI "m\\varbslash"             j (bussProof f) (bussProof g)
        bussProof′ (m⇐   f g) j = BI "m\\varslash"              j (bussProof f) (bussProof g)
        bussProof′ (r⇒⊗  f)   j = UI "r\\varbslash\\varotimes"  j (bussProof f)
        bussProof′ (r⊗⇒  f)   j = UI "r\\varotimes\\varbslash"  j (bussProof f)
        bussProof′ (r⇐⊗  f)   j = UI "r\\varslash\\varotimes"   j (bussProof f)
        bussProof′ (r⊗⇐  f)   j = UI "r\\varotimes\\varslash"   j (bussProof f)
        bussProof′ (m⊕   f g) j = BI "m\\varoplus"              j (bussProof f) (bussProof g)
        bussProof′ (m⇛   f g) j = BI "m\\varobslash"            j (bussProof f) (bussProof g)
        bussProof′ (m⇚   f g) j = BI "m\\varoslash"             j (bussProof f) (bussProof g)
        bussProof′ (r⇛⊕  f)   j = UI "r\\varobslash\\varoplus"  j (bussProof f)
        bussProof′ (r⊕⇛  f)   j = UI "r\\varoplus\\varobslash"  j (bussProof f)
        bussProof′ (r⊕⇚  f)   j = UI "r\\varoplus\\varoslash"   j (bussProof f)
        bussProof′ (r⇚⊕  f)   j = UI "r\\varoslash\\varoplus"   j (bussProof f)
        bussProof′ (d⇛⇐  f)   j = UI "d\\varobslash\\varslash"  j (bussProof f)
        bussProof′ (d⇛⇒  f)   j = UI "d\\varobslash\\varbslash" j (bussProof f)
        bussProof′ (d⇚⇒  f)   j = UI "d\\varoslash\\varbslash"  j (bussProof f)
        bussProof′ (d⇚⇐  f)   j = UI "d\\varoslash\\varslash"   j (bussProof f)
