------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements a proof of equivalence with the de Grootte's SC as `eq`.
------------------------------------------------------------------------


open import Function.Equivalence                       using (_⇔_; equivalence)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module Logic.Intuitionistic.Ordered.Lambek.ResMon.EquivalentToSC {ℓ} (Atom : Set ℓ) where


open import Logic.Intuitionistic.Ordered.Lambek.Type             Atom as NLT
open import Logic.Intuitionistic.Ordered.Lambek.Type.Context     Atom as NLTC hiding (module Simple)
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.Judgement Atom as NLJ
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.Base      Atom as NL
open import Logic.Intuitionistic.Ordered.Lambek.SC.Judgement     Atom as SCJ
open import Logic.Intuitionistic.Ordered.Lambek.SC.Base          Atom as SCB hiding (contᴺ′; contᴾ′) renaming (NL_ to SC_)


module Simple where

  open NLTC.Simple using (_[_]; _<_>; <>-def)

  mutual
    from : ∀ {A B} → SC A ⊢ B → NL A ⊢ B
    from ax = ax
    from (m⊗ f g) = m⊗ (from f) (from g)
    from (m⇒ f g) = m⇒ (from f) (from g)
    from (m⇐ f g) = m⇐ (from f) (from g)
    from (contᴺ f x p _ _) rewrite p = contᴺ′ (from f) x
    from (contᴾ f x p _ _) rewrite p = contᴾ′ (from f) x

    -- Derived version of negative context application for the
    -- residuation-monotonicity calculus (which uses the context
    -- inference rules from the SC calculus).
    contᴺ′ : ∀ {Γ A B} → NL A ⊢ B → SC ⊢ᴺ Γ → NL Γ [ A ] ⊢ B
    contᴺ′ f neg-[] = f
    contᴺ′ {._} {C} {D} f (neg-⊗⇒ {Γ} {Δ} {A} {B} g x y)
      rewrite <>-def Γ (B ⇒> Δ) C
              = r⇒⊗ (contᴺ′ (m⇒ (from g) (contᴺ′ f y)) x)
    contᴺ′ {._} {C} {D} f (neg-⊗⇐ {Γ} {Δ} {A} {B} g x y)
      rewrite <>-def Γ (Δ <⇐ B) C
              = r⇐⊗ (contᴺ′ (m⇐ (contᴺ′ f y) (from g)) x)

    -- Derived version of positive context application for the
    -- residuation-monotonicity calculus (which uses the context
    -- inference rules from the SC calculus).
    contᴾ′ : ∀ {Δ A B} → NL A ⊢ B → SC ⊢ᴾ Δ → NL A ⊢ Δ [ B ]
    contᴾ′ f pos-[] = f
    contᴾ′ {._} {C} {D} f (pos-⇒⊗ {Γ} {Δ} {A} {B} g x y)
      rewrite <>-def Γ (B ⊗> Δ) D
              = r⊗⇒ (contᴾ′ (m⊗ (from g) (contᴾ′ f y)) x)
    contᴾ′ {._} {C} {D} f (pos-⇐⊗ {Γ} {Δ} {A} {B} g x y)
      rewrite <>-def Γ (Δ <⊗ B) D
              = r⊗⇐ (contᴾ′ (m⊗ (contᴾ′ f y) (from g)) x)
    contᴾ′ {._} {C} {D} f (pos-⇐⇒ {Γ} {Δ} {B} {A} g x y)
      rewrite <>-def Γ (Δ <⇒ B) D
              = r⊗⇐ (r⇒⊗ (contᴺ′ (m⇒ (contᴾ′ f y) (from g)) x))
    contᴾ′ {._} {C} {D} f (pos-⇒⇐ {Γ} {Δ} {B} {A} g x y)
      rewrite <>-def Γ (B ⇐> Δ) D
              = r⊗⇒ (r⇐⊗ (contᴺ′ (m⇐ (from g) (contᴾ′ f y)) x))


  to : ∀ {A B} → NL A ⊢ B → SC A ⊢ B
  to ax = ax
  to (m⊗ f g) = m⊗ (to f) (to g)
  to (m⇒ f g) = m⇒ (to f) (to g)
  to (m⇐ f g) = m⇐ (to f) (to g)
  to (r⇒⊗ f) = r⇒⊗′ (to f)
  to (r⊗⇒ f) = r⊗⇒′ (to f)
  to (r⇐⊗ f) = r⇐⊗′ (to f)
  to (r⊗⇐ f) = r⊗⇐′ (to f)


eq : ∀ {A B} → (NL A ⊢ B) ⇔ (SC A ⊢ B)
eq = equivalence to from
  where open Simple
