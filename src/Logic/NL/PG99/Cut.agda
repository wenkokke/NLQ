------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Uses the equivalence relation between PG99 and the
-- residuation-monotonicity axiomatisations to import the proof of
-- transitivity into PG99.
------------------------------------------------------------------------


open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; trans)


module Logic.NL.PG99.Cut {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type                    Atom
open import Logic.NL.Type.Context            Atom
open import Logic.NL.PG99.Sequent          Atom
open import Logic.NL.PG99.Base               Atom
open import Logic.NL.PG99.EquivalentToResMon Atom
open import Logic.NL.ResMon.Cut              Atom as RM hiding (cut′)


cut′ : ∀ {A B C} → NL A ⊢ B → NL B ⊢ C → NL A ⊢ C
cut′ f g = from (RM.cut′ (to f) (to g))
