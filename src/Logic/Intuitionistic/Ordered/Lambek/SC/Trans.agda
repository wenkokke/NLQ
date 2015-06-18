------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Uses the equivalence relation between SC and the
-- residuation-monotonicity axiomatisations to import the proof of
-- transitivity into SC.
------------------------------------------------------------------------


open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; trans)


module Logic.Intuitionistic.Ordered.Lambek.SC.Trans {ℓ} (Atom : Set ℓ) where


open import Logic.Intuitionistic.Ordered.Lambek.Type                  Atom
open import Logic.Intuitionistic.Ordered.Lambek.Type.Context          Atom
open import Logic.Intuitionistic.Ordered.Lambek.SC.Judgement          Atom as SCJ
open import Logic.Intuitionistic.Ordered.Lambek.SC.Base               Atom as SCB
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.EquivalentToSC Atom as SCE
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.Trans          Atom as NLT hiding (trans′)


trans′ : ∀ {A B C} → NL A ⊢ B → NL B ⊢ C → NL A ⊢ C
trans′ f g = to (NLT.trans′ (from f) (from g))
  where open SCE.Simple using (to; from)
