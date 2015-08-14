------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Bool
open import Function using (_$_)
open import Data.Nat
open import Data.String
open import Logic.ToLaTeX
open import Relation.Nullary.Decidable


module Logic.LG.Type.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.LG.Type Atom


instance
  TypeToLaTeX : {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX Type
  TypeToLaTeX = record { toLaTeXPrec = go }
    where
      open ToLaTeX {{...}}

      go : ℕ → Type → String
      go p (el  A) = toLaTeX A
      go p (□   A) = parens ⌊ 40 ≤? p ⌋ $ "\\varbox" ∙ go 40 A
      go p (◇   A) = parens ⌊ 40 ≤? p ⌋ $ "\\vardia" ∙ go 40 A
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
