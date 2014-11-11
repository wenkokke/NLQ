------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module Logic.Lambek.NaturalDeduction.EquivalentToResMon {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type                  Univ as T
open import Logic.Lambek.NaturalDeduction.Base Univ as ND renaming (NL_ to ND_)
open import Logic.Lambek.ResMon                Univ as RM renaming (NL_ to RM_)



module Simple where


  from : ∀ {A B} → ND A ⊢ B → RM A ⊢ B
  from id       = id′
  from (⊗I f g) = mon-⊗ (from f) (from g)
  from (⊗E f g) = RM.trans′ (from f) (from g)
  from (⇒I f)   = res-⊗⇒ (from f)
  from (⇒E f g) = RM.trans′ (mon-⊗ (from f) (from g)) (res-⇒⊗ id′)
  from (⇐I f)   = res-⊗⇐ (from f)
  from (⇐E f g) = RM.trans′ (mon-⊗ (from f) (from g)) (res-⇐⊗ id′)

  to : ∀ {A B} → RM A ⊢ B → ND A ⊢ B
  to id           = id
  to (mon-⊗  f g) = ⊗I (to f) (to g)
  to (mon-⇒  f g) = ⇒I (⇒E (to f) (⇒I (ND.trans′ (⇒E id id) (to g))))
  to (mon-⇐  f g) = ⇐I (⇐E (⇐I (ND.trans′ (⇐E id id) (to f))) (to g))
  to (res-⇒⊗ f)   = ⇒E id (to f)
  to (res-⊗⇒ f)   = ⇒I (to f)
  to (res-⇐⊗ f)   = ⇐E (to f) id
  to (res-⊗⇐ f)   = ⇐I (to f)


ResMon⇔NaturalDeduction : ∀ {A B} → RM A ⊢ B ⇔ ND A ⊢ B
ResMon⇔NaturalDeduction = equivalence to from
  where
    open Simple
