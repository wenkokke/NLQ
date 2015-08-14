--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/EquivalentToFocPol.agda
--------------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Function.Equivalence                       using (_⇔_; equivalence)
open import Data.Product                               using (_×_; proj₁)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable                 using (fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


open import Logic.Polarity
open import Logic.Translation


module Logic.NL.EquivalentToPol
  {ℓ} (Atom : Set ℓ) (Polarityᴬ? : Atom → Polarity) where


open import Logic.NL.Type.Polarised      Atom Polarityᴬ?
open import Logic.NL.Type                Atom
open import Logic.NL.Structure.Polarised Atom
open import Logic.NL.Judgement           Atom
open import Logic.NL.Base                Atom
open import Logic.NL.Pol.Base            Atom Polarityᴬ? renaming (NL_ to fNL_)


from : ∀ {J} → fNL J → NL J
from ax⁺       = ax⁺
from ax⁻       = ax⁻
from (⇁   f)   = ⇁   (from f)
from (↽   f)   = ↽   (from f)
from (⇀   f)   = ⇀   (from f)
from (↼   f)   = ↼   (from f)
from (⊗ᴿ  f g) = ⊗ᴿ  (from f) (from g)
from (⇒ᴸ  f g) = ⇒ᴸ  (from f) (from g)
from (⇐ᴸ  f g) = ⇐ᴸ  (from f) (from g)
from (⊗ᴸ  f)   = ⊗ᴸ  (from f)
from (⇒ᴿ  f)   = ⇒ᴿ  (from f)
from (⇐ᴿ  f)   = ⇐ᴿ  (from f)
from (r⇒⊗ f)   = r⇒⊗ (from f)
from (r⊗⇒ f)   = r⊗⇒ (from f)
from (r⇐⊗ f)   = r⇐⊗ (from f)
from (r⊗⇐ f)   = r⊗⇐ (from f)
