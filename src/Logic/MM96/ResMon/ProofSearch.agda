--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/ProofSearch.agda
--------------------------------------------------------------------------------


open import Category.Monad   using (module RawMonadPlus; RawMonadPlus)
open import Data.Maybe       using (Maybe; From-just; from-just)
open import Data.List        using (List; _∷_; [])
open import Data.List.Any    using (any)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P


module Logic.MM96.ResMon.ProofSearch
       {ℓ} (Atom : Set ℓ) (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B))
       where


open import Logic.MM96.Type             Atom as T
open import Logic.MM96.ResMon.Judgement Atom as J
open import Logic.MM96.ResMon.Base      Atom

open T.DecEq      _≟-Atom_ using (_≟-Type_)
open J.DecEq _≟-Atom_ using (_≟-Judgement_)


{-# TERMINATING #-}
search : {Mon : Set ℓ → Set ℓ} (monadPlus : RawMonadPlus Mon) (J : Judgement) → Mon (MM96 J)
search {Mon} monadPlus = search′ []
  where
  open RawMonadPlus monadPlus using (∅; _∣_; return; _>>=_)

  search′ : (seen : List Judgement) (J : Judgement) → Mon (MM96 J)
  search′ seen J with any (J ≟-Judgement_) seen
  search′ seen J | yes J∈seen = ∅
  search′ seen J | no  J∉seen
    = check-ax J
    ∣ check-m⟨t⟩ J ∣ check-m⟨l⟩ J ∣ check-m⟨r⟩ J
    ∣ check-m◇   J ∣ check-m□   J ∣ check-r◇□  J ∣ check-r□◇  J
    ∣ check-m⊗   J ∣ check-m⇒   J ∣ check-m⇐   J
    ∣ check-r⇒⊗  J ∣ check-r⇐⊗  J ∣ check-r⊗⇒  J ∣ check-r⊗⇐  J
    ∣ check-m⊙   J ∣ check-m⇦   J ∣ check-m⇨   J
    ∣ check-r⇨⊙  J ∣ check-r⊙⇨  J ∣ check-r⇦⊙  J ∣ check-r⊙⇦  J
    ∣ check-p₀   J ∣ check-p₁   J ∣ check-p₂   J
    ∣ check-p₀′  J ∣ check-p₁′  J ∣ check-p₂′  J
    where


    reset    = search′ []         -- for rules which make progress
    continue = search′ (J ∷ seen) -- for rules which make no progress


    check-ax : (J : Judgement) → Mon (MM96 J)
    check-ax (el A ⊢ el B) with A ≟-Atom B
    ... | yes A=B rewrite A=B = return ax
    ... | no  A≠B             = ∅
    check-ax _ = ∅

    -- rules for residuation and monotonicity for (I, ⟨l⟩ , ⟨r⟩)
    check-m⟨t⟩ : (J : Judgement) → Mon (MM96 J)
    check-m⟨t⟩ (⟨t⟩ ⊢ ⟨t⟩) = return m⟨t⟩
    check-m⟨t⟩ _ = ∅
    check-m⟨l⟩ : (J : Judgement) → Mon (MM96 J)
    check-m⟨l⟩  (⟨l⟩ A ⊢ ⟨l⟩ B) = reset (A ⊢ B) >>= λ x → return (m⟨l⟩ x)
    check-m⟨l⟩ _ = ∅
    check-m⟨r⟩ : (J : Judgement) → Mon (MM96 J)
    check-m⟨r⟩  (⟨r⟩ A ⊢ ⟨r⟩ B) = reset (A ⊢ B) >>= λ x → return (m⟨r⟩ x)
    check-m⟨r⟩ _ = ∅

    -- rules for residuation and monotonicity for (□ , ◇)
    check-m□ : (J : Judgement) → Mon (MM96 J)
    check-m□  (□ A ⊢ □ B) = reset (A ⊢ B) >>= λ x → return (m□ x)
    check-m□ _ = ∅
    check-m◇ : (J : Judgement) → Mon (MM96 J)
    check-m◇  (◇ A ⊢ ◇ B) = reset (A ⊢ B) >>= λ x → return (m◇ x)
    check-m◇ _ = ∅
    check-r□◇ : (J : Judgement) → Mon (MM96 J)
    check-r□◇ (◇ A ⊢ B) = continue (A ⊢ □ B) >>= λ x → return (r□◇ x)
    check-r□◇ _ = ∅
    check-r◇□ : (J : Judgement) → Mon (MM96 J)
    check-r◇□ (A ⊢ □ B) = continue (◇ A ⊢ B) >>= λ x → return (r◇□ x)
    check-r◇□ _ = ∅

    -- rules for residuation and monotonicity for (⇐ , ⊗ , ⇒)
    check-m⊗ : (J : Judgement) → Mon (MM96 J)
    check-m⊗ (A ⊗ C ⊢ B ⊗ D) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⊗ x y)
    check-m⊗ _ = ∅
    check-m⇒ : (J : Judgement) → Mon (MM96 J)
    check-m⇒ (B ⇒ C ⊢ A ⇒ D) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⇒ x y)
    check-m⇒ _ = ∅
    check-m⇐ : (J : Judgement) → Mon (MM96 J)
    check-m⇐ (A ⇐ D ⊢ B ⇐ C) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⇐ x y)
    check-m⇐ _ = ∅

    check-r⇒⊗ : (J : Judgement) → Mon (MM96 J)
    check-r⇒⊗ (A ⊗ B ⊢ C) = continue (B ⊢ A ⇒ C) >>= λ x → return (r⇒⊗ x)
    check-r⇒⊗ _  = ∅
    check-r⇐⊗ : (J : Judgement) → Mon (MM96 J)
    check-r⇐⊗ (A ⊗ B ⊢ C) = continue (A ⊢ C ⇐ B) >>= λ x → return (r⇐⊗ x)
    check-r⇐⊗ _  = ∅
    check-r⊗⇒ : (J : Judgement) → Mon (MM96 J)
    check-r⊗⇒ (B ⊢ A ⇒ C) = continue (A ⊗ B ⊢ C) >>= λ x → return (r⊗⇒ x)
    check-r⊗⇒ _  = ∅
    check-r⊗⇐ : (J : Judgement) → Mon (MM96 J)
    check-r⊗⇐ (A ⊢ C ⇐ B) = continue (A ⊗ B ⊢ C) >>= λ x → return (r⊗⇐ x)
    check-r⊗⇐ _  = ∅

    -- rules for residuation and monotonicity for (⇦ , ⊙ , ⇨)
    check-m⊙ : (J : Judgement) → Mon (MM96 J)
    check-m⊙ (A ⊙ C ⊢ B ⊙ D) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⊙ x y)
    check-m⊙ _ = ∅
    check-m⇨ : (J : Judgement) → Mon (MM96 J)
    check-m⇨ (B ⇨ C ⊢ A ⇨ D) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⇨ x y)
    check-m⇨ _ = ∅
    check-m⇦ : (J : Judgement) → Mon (MM96 J)
    check-m⇦ (A ⇦ D ⊢ B ⇦ C) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⇦ x y)
    check-m⇦ _ = ∅

    check-r⇨⊙ : (J : Judgement) → Mon (MM96 J)
    check-r⇨⊙ (A ⊙ B ⊢ C) = continue (B ⊢ A ⇨ C) >>= λ x → return (r⇨⊙ x)
    check-r⇨⊙ _  = ∅
    check-r⇦⊙ : (J : Judgement) → Mon (MM96 J)
    check-r⇦⊙ (A ⊙ B ⊢ C) = continue (A ⊢ C ⇦ B) >>= λ x → return (r⇦⊙ x)
    check-r⇦⊙ _  = ∅
    check-r⊙⇨ : (J : Judgement) → Mon (MM96 J)
    check-r⊙⇨ (B ⊢ A ⇨ C) = continue (A ⊙ B ⊢ C) >>= λ x → return (r⊙⇨ x)
    check-r⊙⇨ _  = ∅
    check-r⊙⇦ : (J : Judgement) → Mon (MM96 J)
    check-r⊙⇦ (A ⊢ C ⇦ B) = continue (A ⊙ B ⊢ C) >>= λ x → return (r⊙⇦ x)
    check-r⊙⇦ _  = ∅

    -- rules for scope taking
    check-p₀  : (J : Judgement) → Mon (MM96 J)
    check-p₀  (A ⊙ ⟨t⟩ ⊢ B) = continue (◇ A ⊢ B) >>= λ x → return (p₀  x)
    check-p₀  _  = ∅
    check-p₀′ : (J : Judgement) → Mon (MM96 J)
    check-p₀′ (◇ A ⊢ B) = continue (A ⊙ ⟨t⟩ ⊢ B) >>= λ x → return (p₀′ x)
    check-p₀′ _  = ∅
    check-p₁  : (J : Judgement) → Mon (MM96 J)
    check-p₁  (A ⊙ ⟨l⟩ (B ⊗ C) ⊢ D) = continue ((A ⊙ B) ⊗ C ⊢ D) >>= λ x → return (p₁  x)
    check-p₁  _  = ∅
    check-p₁′ : (J : Judgement) → Mon (MM96 J)
    check-p₁′ ((A ⊙ B) ⊗ C ⊢ D) = continue (A ⊙ ⟨l⟩ (B ⊗ C) ⊢ D) >>= λ x → return (p₁′ x)
    check-p₁′ _  = ∅
    check-p₂  : (J : Judgement) → Mon (MM96 J)
    check-p₂  (B ⊙ ⟨r⟩ (A ⊗ C) ⊢ D) = continue (A ⊗ (B ⊙ C) ⊢ D) >>= λ x → return (p₂  x)
    check-p₂  _  = ∅
    check-p₂′ : (J : Judgement) → Mon (MM96 J)
    check-p₂′ (A ⊗ (B ⊙ C) ⊢ D) = continue (B ⊙ ⟨r⟩ (A ⊗ C) ⊢ D) >>= λ x → return (p₂′ x)
    check-p₂′ _  = ∅


findMaybe : (J : Judgement) → Maybe (MM96 J)
findMaybe = search Data.Maybe.monadPlus

find : (J : Judgement) → From-just (MM96 J) (findMaybe J)
find J = from-just (findMaybe J)

findAll : (J : Judgement) → List (MM96 J)
findAll = search Data.List.monadPlus
