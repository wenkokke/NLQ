------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Relation.Nullary using (Dec; yes; no)


module Logic.Lambek.Type {ℓ} (Univ : Set ℓ) where


open import Logic.Type Univ


infix 5 is-valid_ is-valid?_


data is-valid_ : Type → Set ℓ where
  el   : (A : Univ) → is-valid (el A)
  _⊗_  : ∀ {A B} → is-valid A → is-valid B → is-valid (A ⊗ B)
  _⇐_  : ∀ {A B} → is-valid A → is-valid B → is-valid (A ⇐ B)
  _⇒_  : ∀ {A B} → is-valid A → is-valid B → is-valid (A ⇒ B)


is-valid?_ : (A : Type) → Dec (is-valid A)
is-valid? (el A)  = yes (el A)
is-valid? (A ⊗ B) with is-valid? A | is-valid? B
is-valid? (_ ⊗ _) | yes A | yes B = yes (A ⊗ B)
is-valid? (_ ⊗ _) | no ¬A | _     = no (λ {(A ⊗ B) → ¬A A})
is-valid? (_ ⊗ _) | _     | no ¬B = no (λ {(A ⊗ B) → ¬B B})
is-valid? (A ⇐ B) with is-valid? A | is-valid? B
is-valid? (_ ⇐ _) | yes A | yes B = yes (A ⇐ B)
is-valid? (_ ⇐ _) | no ¬A | _     = no (λ {(A ⇐ B) → ¬A A})
is-valid? (_ ⇐ _) | _     | no ¬B = no (λ {(A ⇐ B) → ¬B B})
is-valid? (A ⇒ B) with is-valid? A | is-valid? B
is-valid? (_ ⇒ _) | yes A | yes B = yes (A ⇒ B)
is-valid? (_ ⇒ _) | no ¬A | _     = no (λ {(A ⇒ B) → ¬A A})
is-valid? (_ ⇒ _) | _     | no ¬B = no (λ {(A ⇒ B) → ¬B B})
is-valid? (A ⊕ B) = no (λ ())
is-valid? (A ⇚ B) = no (λ ())
is-valid? (A ⇛ B) = no (λ ())
