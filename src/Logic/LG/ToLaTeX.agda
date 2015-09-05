------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.String
open import Logic.ToLaTeX


module Logic.LG.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.LG.Type                        Atom
open import Logic.LG.Type.ToLaTeX                Atom
open import Logic.LG.Structure.Polarised         Atom
open import Logic.LG.Structure.Polarised.ToLaTeX Atom
open import Logic.LG.Sequent                   Atom
open import Logic.LG.Sequent.ToLaTeX           Atom
open import Logic.LG.Base                        Atom


instance
  sLGToLaTeX : ∀ {J} {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (LG J)
  sLGToLaTeX = record { toLaTeXPrec = λ _ → B.toLaTeX ∘ bussProof }
    where
      module B = ToLaTeX BussProofToLaTeX
      module J = ToLaTeX SequentToLaTeX

      mutual
        bussProof : ∀ {J} (f : LG J) → BussProof
        bussProof {J} f = bussProof′ f (J.toLaTeX J)

        bussProof′ : ∀ {J} (f : LG J) → (String → BussProof)
        bussProof′  ax⁺      j = AX "\\text{ax}^+"             j
        bussProof′  ax⁻      j = AX "\\text{ax}^-"             j
        bussProof′ (⇁   f)   j = UI "\\rightharpoondown"       j (bussProof f)
        bussProof′ (↽   f)   j = UI "\\leftharpoondown"        j (bussProof f)
        bussProof′ (⇀   f)   j = UI "\\rightharpoonup"         j (bussProof f)
        bussProof′ (↼   f)   j = UI "\\leftharpoonup"          j (bussProof f)
        bussProof′ (◇L  f)   j = UI "\\vardia L"               j (bussProof f)
        bussProof′ (◇R  f)   j = UI "\\vardia R"               j (bussProof f)
        bussProof′ (□L  f)   j = UI "\\varbox L"               j (bussProof f)
        bussProof′ (□R  f)   j = UI "\\varbox R"               j (bussProof f)
        bussProof′ (r□◇ f)   j = UI "r\\varbox\\vardia"        j (bussProof f)
        bussProof′ (r◇□ f)   j = UI "r\\vardia\\varbox"        j (bussProof f)
        bussProof′ (₀L  f)   j = UI "\\varpref0 L"             j (bussProof f)
        bussProof′ (₀R  f)   j = UI "\\varpref0 R"             j (bussProof f)
        bussProof′ (⁰L  f)   j = UI "\\varsuff0 L"             j (bussProof f)
        bussProof′ (⁰R  f)   j = UI "\\varsuff0 R"             j (bussProof f)
        bussProof′ (₁L  f)   j = UI "\\varpref1 L"             j (bussProof f)
        bussProof′ (₁R  f)   j = UI "\\varpref1 R"             j (bussProof f)
        bussProof′ (¹L  f)   j = UI "\\varsuff1 L"             j (bussProof f)
        bussProof′ (¹R  f)   j = UI "\\varsuff1 R"             j (bussProof f)
        bussProof′ (r⁰₀ f)   j = UI "r\\varsuff0\\varpref0"    j (bussProof f)
        bussProof′ (r₀⁰ f)   j = UI "r\\varpref0\\varsuff0"    j (bussProof f)
        bussProof′ (r¹₁ f)   j = UI "r\\varsuff1\\varpref1"    j (bussProof f)
        bussProof′ (r₁¹ f)   j = UI "r\\varpref1\\varsuff1"    j (bussProof f)
        bussProof′ (⊗L  f)   j = UI "\\varotimes L"            j (bussProof f)
        bussProof′ (⊗R  f g) j = BI "\\varotimes R"            j (bussProof f) (bussProof g)
        bussProof′ (⇒L  f g) j = BI "\\varbslash L"            j (bussProof f) (bussProof g)
        bussProof′ (⇒R  f)   j = UI "\\varbslash R"            j (bussProof f)
        bussProof′ (⇐L  f g) j = BI "\\varslash L"             j (bussProof f) (bussProof g)
        bussProof′ (⇐R  f)   j = UI "\\varslash R"             j (bussProof f)
        bussProof′ (r⇒⊗ f)   j = UI "r\\varbslash\\varotimes"  j (bussProof f)
        bussProof′ (r⊗⇒ f)   j = UI "r\\varotimes\\varbslash"  j (bussProof f)
        bussProof′ (r⇐⊗ f)   j = UI "r\\varslash\\varotimes"   j (bussProof f)
        bussProof′ (r⊗⇐ f)   j = UI "r\\varotimes\\varslash"   j (bussProof f)
        bussProof′ (⊕L  f g) j = BI "\\varoplus L"             j (bussProof f) (bussProof g)
        bussProof′ (⊕R  f)   j = UI "\\varoplus R"             j (bussProof f)
        bussProof′ (⇚L  f)   j = UI "\\varoslash L"            j (bussProof f)
        bussProof′ (⇚R  f g) j = BI "\\varoslash R"            j (bussProof f) (bussProof g)
        bussProof′ (⇛L  f)   j = UI "\\varobslash L"           j (bussProof f)
        bussProof′ (⇛R  f g) j = BI "\\varobslash R"           j (bussProof f) (bussProof g)
        bussProof′ (r⇚⊕ f)   j = UI "r\\varoslash\\varoplus"   j (bussProof f)
        bussProof′ (r⊕⇚ f)   j = UI "r\\varoplus\\varoslash"   j (bussProof f)
        bussProof′ (r⇛⊕ f)   j = UI "r\\varobslash\\varoplus"  j (bussProof f)
        bussProof′ (r⊕⇛ f)   j = UI "r\\varoplus\\varobslash"  j (bussProof f)
        bussProof′ (d⇛⇐ f)   j = UI "d\\varobslash\\varslash"  j (bussProof f)
        bussProof′ (d⇛⇒ f)   j = UI "d\\varobslash\\varbslash" j (bussProof f)
        bussProof′ (d⇚⇒ f)   j = UI "d\\varoslash\\varbslash"  j (bussProof f)
        bussProof′ (d⇚⇐ f)   j = UI "d\\varoslash\\varslash"   j (bussProof f)
