------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Bool
open import Function using (_$_)
open import Data.Nat
open import Data.String
open import Logic.ToLaTeX
open import Relation.Nullary.Decidable


module Logic.Classical.Ordered.LambekGrishin.Structure.ToLaTeX {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type         Univ
open import Logic.Classical.Ordered.LambekGrishin.Type.ToLaTeX Univ
open import Logic.Classical.Ordered.LambekGrishin.Structure    Univ


instance
  StructureToLaTeX : {{UnivToLaTeX : ToLaTeX Univ}} → ToLaTeX Structure
  StructureToLaTeX = record { toLaTeXPrec = go }
    where
      open ToLaTeX {{...}}

      go : ℕ → Structure → String
      go _ ·  A  · = "\\vardown{" ++ toLaTeX A ++ "}"
      go _ [  X  ] = "\\varbox[" ++ go 0 X ++ "]"
      go _ ⟨  X  ⟩ = "\\vardia[" ++ go 0 X ++ "]"
      go p (₀   A) = parens ⌊ 40 ≤? p ⌋ $ "\\varpref0" ∙ go 40 A
      go p (A   ⁰) = parens ⌊ 40 ≤? p ⌋ $ go 40 A ∙ "\\varsuff0"
      go p (₁   A) = parens ⌊ 40 ≤? p ⌋ $ "\\varpref1" ∙ go 40 A
      go p (A   ¹) = parens ⌊ 40 ≤? p ⌋ $ go 40 A ∙ "\\varsuff1"
      go p (A ⊗ B) = parens ⌊ 30 ≤? p ⌋ $ go 30 A ∙ "\\varotimes"  ∙ go 29 B
      go p (A ⇒ B) = parens ⌊ 20 ≤? p ⌋ $ go 20 A ∙ "\\varbslash"  ∙ go 20 B
      go p (B ⇐ A) = parens ⌊ 20 ≤? p ⌋ $ go 20 B ∙ "\\varslash"   ∙ go 20 A
      go p (B ⊕ A) = parens ⌊ 30 ≤? p ⌋ $ go 29 B ∙ "\\varoplus"   ∙ go 30 A
      go p (B ⇚ A) = parens ⌊ 25 ≤? p ⌋ $ go 25 B ∙ "\\varoslash"  ∙ go 25 A
      go p (A ⇛ B) = parens ⌊ 25 ≤? p ⌋ $ go 25 A ∙ "\\varobslash" ∙ go 25 B
