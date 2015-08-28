--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/Structure/ToLaTeX.agda
--------------------------------------------------------------------------------


open import Data.Bool
open import Function using (_$_)
open import Data.Nat
open import Data.String
open import Logic.ToLaTeX
open import Relation.Nullary.Decidable


module Logic.NLCPS.Structure.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.NLCPS.Type         Atom
open import Logic.NLCPS.Type.ToLaTeX Atom
open import Logic.NLCPS.Structure    Atom


instance
  StructureToLaTeX : {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX Structure
  StructureToLaTeX = record { toLaTeXPrec = go }
    where
      open ToLaTeX {{...}}

      go : ℕ → Structure → String
      go _ ·  A  · = "\\vardown{" ++ toLaTeX A ++ "}"
      go _  ⟨ X ⟩  = "\\vardia[" ++ go 0 X ++ "]"
      go p (A ⊗ B) = parens ⌊ 30 ≤? p ⌋ $ go 30 A ∙ "\\varotimes"  ∙ go 29 B
      go p (A ⇒ B) = parens ⌊ 20 ≤? p ⌋ $ go 20 A ∙ "\\varbslash"  ∙ go 20 B
      go p (B ⇐ A) = parens ⌊ 20 ≤? p ⌋ $ go 20 B ∙ "\\varslash"   ∙ go 20 A
