------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality as P using (_≡_)


module Logic.Linear.NaturalDeduction.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Linear.Type                               Univ as T
open import Logic.Linear.NaturalDeduction.Structure         Univ as NDS
open import Logic.Linear.NaturalDeduction.Structure.Context Univ as NDSC
open import Logic.Linear.NaturalDeduction.Judgement         Univ as NDJ


infix 3 LL_

data LL_ : Judgement → Set ℓ where
  id   : ∀ {A}         → LL A , ∅ ⊢ A
  ⇒I   : ∀ {X A B}     → LL A , X ⊢ B → LL X ⊢ A ⇒ B
  ⇒E   : ∀ {X Y A B}   → LL X ⊢ A ⇒ B → LL Y ⊢ A → LL X ++ Y ⊢ B
  ⊗I   : ∀ {X Y A B}   → LL X ⊢ A → LL Y ⊢ B → LL X ++ Y ⊢ A ⊗ B
  ⊗E   : ∀ {X Y A B C} → LL X ⊢ A ⊗ B → LL A , B , Y ⊢ C → LL X ++ Y ⊢ C
  exch : ∀ {X Y Z W A} → LL (X ++ Z) ++ (Y ++ W) ⊢ A
                       → LL (X ++ Y) ++ (Z ++ W) ⊢ A


exch₀ : ∀ {X A B C} → LL A , B , X ⊢ C → LL B , A , X ⊢ C
exch₀ {X} {A} {B} f = exch {∅} {B , ∅} {A , ∅} {X} f

⊗L : ∀ {X A B C} → LL A , B , X ⊢ C → LL A ⊗ B , X ⊢ C
⊗L f = ⊗E id f
