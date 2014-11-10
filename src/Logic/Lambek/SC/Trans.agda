------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Uses the equivalence relation between SC and the
-- residuation-monotonicity axiomatisations to import the proof of
-- transitivity into SC.
------------------------------------------------------------------------


open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; trans)


module Logic.Lambek.SC.Trans {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type                  Univ
open import Logic.Lambek.Type.Context          Univ
open import Logic.Lambek.SC.Judgement          Univ as SCJ
open import Logic.Lambek.SC.Base               Univ as SCB
open import Logic.Lambek.SC.EquivalentToResMon Univ as SCE
open import Logic.Lambek.ResMon.Trans          Univ as RMT hiding (trans′)

open SCE.Simple using (to; from)

trans′ : ∀ {A B C} → NL A ⊢ B → NL B ⊢ C → NL A ⊢ C
trans′ f g = to (RMT.trans′ (from f) (from g))
