------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements a proof of equivalence with the residuation-monotonicity
-- calculus as `eq`.
------------------------------------------------------------------------


open import Function.Equivalence                       using (_⇔_; equivalence)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module Logic.Intuitionistic.Ordered.Lambek.ResMon.EquivalentToSC {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Ordered.Lambek.Type             Univ as NLT
open import Logic.Intuitionistic.Ordered.Lambek.Type.Context     Univ as NLTC hiding (module Simple)
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.Judgement Univ as NLJ
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.Base      Univ as NL
open import Logic.Intuitionistic.Ordered.Lambek.SC.Judgement     Univ as SCJ
open import Logic.Intuitionistic.Ordered.Lambek.SC.Base          Univ as SCB hiding (contᴺ′; contᴾ′) renaming (NL_ to SC_)


module Simple where

  open NLTC.Simple using (_[_]; _<_>; <>-def)

  mutual
    from : ∀ {A B} → SC A ⊢ B → NL A ⊢ B
    from ax = ax
    from (mon-⊗ f g) = mon-⊗ (from f) (from g)
    from (mon-⇒ f g) = mon-⇒ (from f) (from g)
    from (mon-⇐ f g) = mon-⇐ (from f) (from g)
    from (contᴺ f x p _ _) rewrite p = contᴺ′ (from f) x
    from (contᴾ f x p _ _) rewrite p = contᴾ′ (from f) x

    -- Derived version of negative context application for the
    -- residuation-monotonicity calculus (which uses the context
    -- inference rules from the SC calculus).
    contᴺ′ : ∀ {Γ A B} → NL A ⊢ B → SC ⊢ᴺ Γ → NL Γ [ A ] ⊢ B
    contᴺ′ f neg-[] = f
    contᴺ′ {._} {C} {D} f (neg-⊗⇒ {Γ} {Δ} {A} {B} g x y)
      rewrite <>-def Γ (B ⇒> Δ) C
              = res-⇒⊗ (contᴺ′ (mon-⇒ (from g) (contᴺ′ f y)) x)
    contᴺ′ {._} {C} {D} f (neg-⊗⇐ {Γ} {Δ} {A} {B} g x y)
      rewrite <>-def Γ (Δ <⇐ B) C
              = res-⇐⊗ (contᴺ′ (mon-⇐ (contᴺ′ f y) (from g)) x)

    -- Derived version of positive context application for the
    -- residuation-monotonicity calculus (which uses the context
    -- inference rules from the SC calculus).
    contᴾ′ : ∀ {Δ A B} → NL A ⊢ B → SC ⊢ᴾ Δ → NL A ⊢ Δ [ B ]
    contᴾ′ f pos-[] = f
    contᴾ′ {._} {C} {D} f (pos-⇒⊗ {Γ} {Δ} {A} {B} g x y)
      rewrite <>-def Γ (B ⊗> Δ) D
              = res-⊗⇒ (contᴾ′ (mon-⊗ (from g) (contᴾ′ f y)) x)
    contᴾ′ {._} {C} {D} f (pos-⇐⊗ {Γ} {Δ} {A} {B} g x y)
      rewrite <>-def Γ (Δ <⊗ B) D
              = res-⊗⇐ (contᴾ′ (mon-⊗ (contᴾ′ f y) (from g)) x)
    contᴾ′ {._} {C} {D} f (pos-⇐⇒ {Γ} {Δ} {B} {A} g x y)
      rewrite <>-def Γ (Δ <⇒ B) D
              = res-⊗⇐ (res-⇒⊗ (contᴺ′ (mon-⇒ (contᴾ′ f y) (from g)) x))
    contᴾ′ {._} {C} {D} f (pos-⇒⇐ {Γ} {Δ} {B} {A} g x y)
      rewrite <>-def Γ (B ⇐> Δ) D
              = res-⊗⇒ (res-⇐⊗ (contᴺ′ (mon-⇐ (from g) (contᴾ′ f y)) x))


  to : ∀ {A B} → NL A ⊢ B → SC A ⊢ B
  to ax = ax
  to (mon-⊗ f g) = mon-⊗ (to f) (to g)
  to (mon-⇒ f g) = mon-⇒ (to f) (to g)
  to (mon-⇐ f g) = mon-⇐ (to f) (to g)
  to (res-⇒⊗ f) = res-⇒⊗′ (to f)
  to (res-⊗⇒ f) = res-⊗⇒′ (to f)
  to (res-⇐⊗ f) = res-⇐⊗′ (to f)
  to (res-⊗⇐ f) = res-⊗⇐′ (to f)


eq : ∀ {A B} → (NL A ⊢ B) ⇔ (SC A ⊢ B)
eq = equivalence to from
  where open Simple
