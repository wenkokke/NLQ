------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements several views on proofs in the system ResMon which are
-- heavily used in the proof of admissibility of the transitivity rule.
--
-- One advantage of the residuation-monotonicity calculus is that
-- every connective *must* be introduced by an application of the
-- corresponding monotonicity-rule. The proofs in the `Origin` module
-- can be used to construct a view on a proof that makes this
-- introducing application of a monotonicity-rule explicit.
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


module Logic.Lambek.ResMon.Origin {ℓ} (Univ : Set ℓ) where


open import Logic.Type Univ
open import Logic.Type.Context Univ
open import Logic.Lambek.Type Univ
open import Logic.Judgement Type Type
open import Logic.Judgement.Context Univ
open import Logic.Lambek.ResMon.Base Univ
open import Logic.Lambek.ResMon.Derivation Univ


-- The origin of a ⊗-connective implements the following view:
--
--    h₁ : E ⊢ B     h₂ : F ⊢ C
--    -------------------------
--     h₁ ⊗ h₂ : E ⊗ F ⊢ B ⊗ C
--                ⋮
--     -----------------------
--     f (h₁ ⊗ h₂) : A ⊢ B ⊗ C
--
-- In other words, every ⊗-connective on the right-hand side of the
-- turnstile was originally introduced by an application of the mon-⊗
-- rule.
--
-- This principle can be generalised to include ⊗-connectives which
-- occur in any output position, i.e. nested in an output context on
-- the right-hand side of the turnstile.
-- An output context O here is any context built up as follows, where
-- F is an arbitrary formula:
--
--    O ≔ [] | F ⇒ O | O ⇐ F
--

--data Origin-⊗ {J} (D⁻ : is-output-rhs D) (f : NL A ⊢ D [ B ⊗ C ]) : Set ℓ where
--  origin-⊗ : ∀ {E F} (h₁ : NL E ⊢ B) (h₂ : NL F ⊢ C)
--                     (f′ : ∀ {G} → NL E ⊗ F ⊢ G ⋯ A ⊢ D [ G ])
--                     (eq : f ≡ f′ $ mon-⊗ h₁ h₂)
--                     → Origin-⊗ D⁻ f
