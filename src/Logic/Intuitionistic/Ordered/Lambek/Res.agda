------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (id)
open import Function.Equivalence using (_⇔_; equivalence)


module Logic.Intuitionistic.Ordered.Lambek.Res {ℓ} (Atom : Set ℓ) where


open import Logic.Intuitionistic.Ordered.Lambek.Type             Atom
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.Judgement Atom public hiding (module DecEq)


infix 1 NL_

data NL_ : Judgement → Set ℓ where
  ax   : ∀ {A}      → NL A ⊢ A
  cut  : ∀ {A B C}  → NL A ⊢ B → NL B ⊢ C → NL A ⊢ C
  r⇒⊗  : ∀ {A B C}  → NL B ⊢ A ⇒ C → NL A ⊗ B ⊢ C
  r⊗⇒  : ∀ {A B C}  → NL A ⊗ B ⊢ C → NL B ⊢ A ⇒ C
  r⇐⊗  : ∀ {A B C}  → NL A ⊢ C ⇐ B → NL A ⊗ B ⊢ C
  r⊗⇐  : ∀ {A B C}  → NL A ⊗ B ⊢ C → NL A ⊢ C ⇐ B


m⊗′  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⊗ C ⊢ B ⊗ D
m⊗′  f g  = r⇐⊗ (cut f (r⊗⇐ (r⇒⊗ (cut g (r⊗⇒ ax)))))

m⇒′  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL B ⇒ C ⊢ A ⇒ D
m⇒′  f g  = r⊗⇒ (cut (r⇐⊗ (cut f (r⊗⇐ (r⇒⊗ ax)))) g)

m⇐′  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⇐ D ⊢ B ⇐ C
m⇐′  f g  = r⊗⇐ (cut (r⇒⊗ (cut g (r⊗⇒ (r⇐⊗ ax)))) f)
