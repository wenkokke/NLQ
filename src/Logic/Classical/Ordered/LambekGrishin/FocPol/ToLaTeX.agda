------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function     using (_∘_)
open import Data.Product using (_×_; _,_)
open import Data.String



module Logic.Classical.Ordered.LambekGrishin.FocPol.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.ToLaTeX
open import Logic.Polarity
open import Logic.Polarity.ToLaTeX                                   Atom
open import Logic.Classical.Ordered.LambekGrishin.FocPol.Base        Atom
open import Logic.Classical.Ordered.LambekGrishin.ToLaTeX            (Polarity × Atom)
open import Logic.Classical.Ordered.LambekGrishin.EquivalentToFocPol Atom


instance
  PolarisedLambekGrishinToLaTeX : ∀ {J} {{AtomToLaTeX : ToLaTeX Atom}} → ToLaTeX (LG J)
  PolarisedLambekGrishinToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX ∘ from }
    where
      open ToLaTeX {{...}}
