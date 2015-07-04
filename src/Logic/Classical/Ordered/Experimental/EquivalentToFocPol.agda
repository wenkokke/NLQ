--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/Classical/Ordered/LambekGrishin/EquivalentToFocPol.agda
--------------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Function.Equivalence                       using (_⇔_; equivalence)
open import Data.Product                               using (_×_; proj₁)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable                 using (fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


open import Logic.Polarity
open import Logic.Translation


module Logic.Classical.Ordered.Experimental.EquivalentToFocPol {ℓ} (Atom : Set ℓ) where


open import Logic.Classical.Ordered.Experimental.Type.Polarised      (Polarity × Atom) proj₁
open import Logic.Classical.Ordered.Experimental.Type                (Polarity × Atom)
open import Logic.Classical.Ordered.Experimental.Structure.Polarised (Polarity × Atom)
open import Logic.Classical.Ordered.Experimental.Judgement           (Polarity × Atom)
open import Logic.Classical.Ordered.Experimental.Base                (Polarity × Atom)
open import Logic.Classical.Ordered.Experimental.FocPol.Base         Atom renaming (EXP_ to EXPᴾᴼᴸ_)


from : ∀ {J} → EXPᴾᴼᴸ J → EXP J
from ax⁺       = ax⁺
from ax⁻       = ax⁻
from (⇁   f)   = ⇁   (from f)
from (↽   f)   = ↽   (from f)
from (⇀   f)   = ⇀   (from f)
from (↼   f)   = ↼   (from f)
from (◇ᴸ  f)   = ◇ᴸ  (from f)
from (◇ᴿ  f)   = ◇ᴿ  (from f)
from (□ᴸ  f)   = □ᴸ  (from f)
from (□ᴿ  f)   = □ᴿ  (from f)
from (⊗ᴿ  f g) = ⊗ᴿ  (from f) (from g)
from (⇚ᴿ  f g) = ⇚ᴿ  (from f) (from g)
from (⇛ᴿ  f g) = ⇛ᴿ  (from f) (from g)
from (⊕ᴸ  f g) = ⊕ᴸ  (from f) (from g)
from (⇒ᴸ  f g) = ⇒ᴸ  (from f) (from g)
from (⇐ᴸ  f g) = ⇐ᴸ  (from f) (from g)
from (⊗ᴸ  f)   = ⊗ᴸ  (from f)
from (⇚ᴸ  f)   = ⇚ᴸ  (from f)
from (⇛ᴸ  f)   = ⇛ᴸ  (from f)
from (⊕ᴿ  f)   = ⊕ᴿ  (from f)
from (⇒ᴿ  f)   = ⇒ᴿ  (from f)
from (⇐ᴿ  f)   = ⇐ᴿ  (from f)
from (r⇒⊗ f)   = r⇒⊗ (from f)
from (r⊗⇒ f)   = r⊗⇒ (from f)
from (r⇐⊗ f)   = r⇐⊗ (from f)
from (r⊗⇐ f)   = r⊗⇐ (from f)
from (r⇚⊕ f)   = r⇚⊕ (from f)
from (r⊕⇚ f)   = r⊕⇚ (from f)
from (r⇛⊕ f)   = r⇛⊕ (from f)
from (r⊕⇛ f)   = r⊕⇛ (from f)
from (d⇛⇐ f)   = d⇛⇐ (from f)
from (d⇛⇒ f)   = d⇛⇒ (from f)
from (d⇚⇒ f)   = d⇚⇒ (from f)
from (d⇚⇐ f)   = d⇚⇐ (from f)
