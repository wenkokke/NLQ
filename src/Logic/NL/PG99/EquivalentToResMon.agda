------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                              using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)


module Logic.NL.PG99.EquivalentToResMon {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type             Atom
open import Logic.NL.Type.Context     Atom as C; open C.Simple using (_[_]; _<_>; <>-def)
open import Logic.NL.ResMon.Sequent Atom as RM
open import Logic.NL.ResMon           Atom renaming (_⊢NL_ to _⊢RM_)
open import Logic.NL.PG99.Sequent   Atom as PG99
open import Logic.NL.PG99.Base        Atom
     renaming (_⊢NL_ to _⊢PG_; ⊢NLᴺ_ to ⊢PGᴺ; ⊢NLᴾ_ to ⊢PGᴾ_) hiding (contᴺ′; contᴾ′)


from : ∀ {A B} → A ⊢RM B → A ⊢PG B
from  ax       = ax
from (m⊗  f g) = m⊗ (from f) (from g)
from (m⇒  f g) = m⇒ (from f) (from g)
from (m⇐  f g) = m⇐ (from f) (from g)
from (r⇒⊗ f)   = r⇒⊗′ (from f)
from (r⊗⇒ f)   = r⊗⇒′ (from f)
from (r⇐⊗ f)   = r⇐⊗′ (from f)
from (r⊗⇐ f)   = r⊗⇐′ (from f)


mutual
  to : ∀ {A B} → A ⊢PG B → A ⊢RM B
  to  ax                         = ax
  to (m⊗    f g)                 = m⊗ (to f) (to g)
  to (m⇒    f g)                 = m⇒ (to f) (to g)
  to (m⇐    f g)                 = m⇐ (to f) (to g)
  to (contᴺ f g p _ _) rewrite p = contᴺ′ (to f) g
  to (contᴾ f g p _ _) rewrite p = contᴾ′ (to f) g

  -- Derived version of negative context application for the
  -- residuation-monotonicity calculus (which uses the context
  -- inference rules from the SC calculus).
  contᴺ′ : ∀ {Γ A B} → A ⊢RM B → ⊢PGᴺ Γ → Γ [ A ] ⊢RM B
  contᴺ′ f neg-[] = f
  contᴺ′ {._} {C} {D} f (neg-⊗⇒ {Γ} {Δ} {A} {B} g x y)
    rewrite <>-def Γ (B ⇒> Δ) C
            = r⇒⊗ (contᴺ′ (m⇒ (to g) (contᴺ′ f y)) x)
  contᴺ′ {._} {C} {D} f (neg-⊗⇐ {Γ} {Δ} {A} {B} g x y)
    rewrite <>-def Γ (Δ <⇐ B) C
            = r⇐⊗ (contᴺ′ (m⇐ (contᴺ′ f y) (to g)) x)

  -- Derived version of positive context application for the
  -- residuation-monotonicity calculus (which uses the context
  -- inference rules from the SC calculus).
  contᴾ′ : ∀ {Δ A B} → A ⊢RM B → ⊢PGᴾ Δ → A ⊢RM Δ [ B ]
  contᴾ′ f pos-[] = f
  contᴾ′ {._} {C} {D} f (pos-⇒⊗ {Γ} {Δ} {A} {B} g x y)
    rewrite <>-def Γ (B ⊗> Δ) D
            = r⊗⇒ (contᴾ′ (m⊗ (to g) (contᴾ′ f y)) x)
  contᴾ′ {._} {C} {D} f (pos-⇐⊗ {Γ} {Δ} {A} {B} g x y)
    rewrite <>-def Γ (Δ <⊗ B) D
            = r⊗⇐ (contᴾ′ (m⊗ (contᴾ′ f y) (to g)) x)
  contᴾ′ {._} {C} {D} f (pos-⇐⇒ {Γ} {Δ} {B} {A} g x y)
    rewrite <>-def Γ (Δ <⇒ B) D
            = r⊗⇐ (r⇒⊗ (contᴺ′ (m⇒ (contᴾ′ f y) (to g)) x))
  contᴾ′ {._} {C} {D} f (pos-⇒⇐ {Γ} {Δ} {B} {A} g x y)
    rewrite <>-def Γ (B ⇐> Δ) D
            = r⊗⇒ (r⇐⊗ (contᴺ′ (m⇐ (to g) (contᴾ′ f y)) x))
