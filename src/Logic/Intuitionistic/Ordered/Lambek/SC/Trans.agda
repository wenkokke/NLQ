------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Uses the equivalence relation between SC and the
-- residuation-monotonicity axiomatisations to import the proof of
-- transitivity into SC.
------------------------------------------------------------------------


open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; trans)


module Logic.Intuitionistic.Ordered.Lambek.SC.Trans {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Ordered.Lambek.Type           Univ
open import Logic.Intuitionistic.Ordered.Lambek.Type.Context   Univ
open import Logic.Intuitionistic.Ordered.Lambek.SC.Judgement   Univ as SCJ
open import Logic.Intuitionistic.Ordered.Lambek.SC.Base        Univ as SCB
open import Logic.Intuitionistic.Ordered.Lambek.EquivalentToSC Univ as SCE
open import Logic.Intuitionistic.Ordered.Lambek.Trans          Univ as NLT hiding (trans′)


trans′ : ∀ {A B C} → NL A ⊢ B → NL B ⊢ C → NL A ⊢ C
trans′ f g = to (NLT.trans′ (from f) (from g))
  where open SCE.Simple using (to; from)
