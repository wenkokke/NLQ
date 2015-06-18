------------------------------------------------------------------------
-- The Lambek Calculus in Agda
-- This file was automatically generated.
------------------------------------------------------------------------


open import Algebra                                    using (module Monoid)
open import Function                                   using (_∘_)
open import Data.List                                  using (List; _++_) renaming ([] to ∅; _∷_ to _,_)
open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; subst; subst₂)


module Logic.Intuitionistic.Linear.Lambda.EquivalentToSequentCalculus {ℓ} (Atom : Set ℓ) where


open import Logic.Intuitionistic.Linear.Lambda.Type                 Atom
open import Logic.Intuitionistic.Linear.Lambda.Judgement            Atom
open import Logic.Intuitionistic.Linear.Lambda.Base                 Atom as Λ
open import Logic.Intuitionistic.Linear.Lambda.Permute              Atom
open import Logic.Intuitionistic.Linear.Lambda.SequentCalculus.Base Atom as ILL


from : ∀ {J} → ILL J → Λ J
from ax            = ax
from (cut {Γ} f g) = cut′ (from f) (from g)
from (⇒ᴸ  {Γ} f g) = cut′ (⇒ₑ ax (from f)) (from g)
from (⇒ᴿ      f)   = ⇒ᵢ (from f)
from (⊗ᴸ      f)   = ⊗ₑ ax (from f)
from (⊗ᴿ      f g) = ⊗ᵢ (from f) (from g)
from (eᴸ Γ₁ Γ₂ Γ₃ Γ₄ f) = eᴸ Γ₁ Γ₂ Γ₃ Γ₄ (from f)


-- to : ∀ {J} → Λ J → ILL J
-- to ax                 = ax
-- to (⇒ᵢ     f)         = ⇒ᴿ (to f)
-- to (⇒ₑ {Γ} f g)       = ILL.sᴸ Γ (cut (to g) {!⇒ᴸ ? ?!})
-- to (⊗ᵢ     f g)       = ⊗ᴿ (to f) (to g)
-- to (⊗ₑ     f g)       = cut (to f) (⊗ᴸ (to g))
-- to (eᴸ Γ₁ Γ₂ Γ₃ Γ₄ f) = eᴸ Γ₁ Γ₂ Γ₃ Γ₄ (to f)
