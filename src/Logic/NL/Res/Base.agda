------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (id)
open import Function.Equivalence using (_⇔_; equivalence)


module Logic.NL.Res.Base {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type          Atom
open import Logic.NL.Res.Judgement Atom public hiding (module DecEq)


infix 1 NL_ _⊢NL_


mutual
  _⊢NL_ : Type → Type → Set ℓ
  A ⊢NL B = NL A ⊢ B

  data NL_ : Judgement → Set ℓ where
    ax   : ∀ {A}      → A ⊢NL A
    cut  : ∀ {A B C}  → A ⊢NL B → B ⊢NL C → A ⊢NL C
    r⇒⊗  : ∀ {A B C}  → B ⊢NL A ⇒ C → A ⊗ B ⊢NL C
    r⊗⇒  : ∀ {A B C}  → A ⊗ B ⊢NL C → B ⊢NL A ⇒ C
    r⇐⊗  : ∀ {A B C}  → A ⊢NL C ⇐ B → A ⊗ B ⊢NL C
    r⊗⇐  : ∀ {A B C}  → A ⊗ B ⊢NL C → A ⊢NL C ⇐ B


m⊗′  : ∀ {A B C D} → A ⊢NL B → C ⊢NL D → A ⊗ C ⊢NL B ⊗ D
m⊗′  f g  = r⇐⊗ (cut f (r⊗⇐ (r⇒⊗ (cut g (r⊗⇒ ax)))))

m⇒′  : ∀ {A B C D} → A ⊢NL B → C ⊢NL D → B ⇒ C ⊢NL A ⇒ D
m⇒′  f g  = r⊗⇒ (cut (r⇐⊗ (cut f (r⊗⇐ (r⇒⊗ ax)))) g)

m⇐′  : ∀ {A B C D} → A ⊢NL B → C ⊢NL D → A ⇐ D ⊢NL B ⇐ C
m⇐′  f g  = r⊗⇐ (cut (r⇒⊗ (cut g (r⊗⇒ (r⇐⊗ ax)))) f)
