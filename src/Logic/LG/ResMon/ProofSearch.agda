------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Category.Monad   using (module RawMonadPlus; RawMonadPlus)
open import Data.Maybe       using (Maybe; From-just; from-just)
open import Data.List        using (List; _∷_; [])
open import Data.List.Any    using (any)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P


module Logic.LG.ResMon.ProofSearch
       {ℓ} (Atom : Set ℓ) (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B))
       where


open import Logic.LG.Type             Atom as T
open import Logic.LG.ResMon.Sequent Atom as J
open import Logic.LG.ResMon.Base      Atom

open T.DecEq      _≟-Atom_ using (_≟-Type_)
open J.DecEq _≟-Atom_ using (_≟-Sequent_)


{-# TERMINATING #-}
search : {Mon : Set ℓ → Set ℓ} (monadPlus : RawMonadPlus Mon) (J : Sequent) → Mon (LG J)
search {Mon} monadPlus = search′ []
  where
  open RawMonadPlus monadPlus using (∅; _∣_; return; _>>=_)

  search′ : (seen : List Sequent) (J : Sequent) → Mon (LG J)
  search′ seen J with any (J ≟-Sequent_) seen
  search′ seen J | yes J∈seen = ∅
  search′ seen J | no  J∉seen
    = check-ax J
    ∣ check-m□  J
    ∣ check-m◇  J
    ∣ check-r□◇ J
    ∣ check-r◇□ J
    ∣ check-m⁰  J ∣ check-m₀  J ∣ check-r⁰₀ J ∣ check-r₀⁰ J
    ∣ check-m¹  J ∣ check-m¹  J ∣ check-r¹₁ J ∣ check-r₁¹ J
    ∣ check-m⊗  J ∣ check-m⇒  J ∣ check-m⇐  J
    ∣ check-r⇒⊗ J ∣ check-r⇐⊗ J ∣ check-r⊗⇒ J ∣ check-r⊗⇐ J
    ∣ check-m⊕  J ∣ check-m⇚  J ∣ check-m⇛  J
    ∣ check-r⇛⊕ J ∣ check-r⊕⇛ J ∣ check-r⇚⊕ J ∣ check-r⊕⇚ J
    where


    reset    = search′ []         -- for rules which make progress
    continue = search′ (J ∷ seen) -- for rules which make no progress


    check-ax : (J : Sequent) → Mon (LG J)
    check-ax (el A ⊢ el B) with A ≟-Atom B
    ... | yes A=B rewrite A=B = return ax
    ... | no  A≠B             = ∅
    check-ax _ = ∅

    -- rules for residuation and monotonicity for (□ , ◇)
    check-m□ : (J : Sequent) → Mon (LG J)
    check-m□  (□ A ⊢ □ B) = reset (A ⊢ B) >>= λ x → return (m□ x)
    check-m□ _ = ∅

    check-m◇ : (J : Sequent) → Mon (LG J)
    check-m◇  (◇ A ⊢ ◇ B) = reset (A ⊢ B) >>= λ x → return (m◇ x)
    check-m◇ _ = ∅

    check-r□◇ : (J : Sequent) → Mon (LG J)
    check-r□◇ (◇ A ⊢ B) = continue (A ⊢ □ B) >>= λ x → return (r□◇ x)
    check-r□◇ _ = ∅

    check-r◇□ : (J : Sequent) → Mon (LG J)
    check-r◇□ (A ⊢ □ B) = continue (◇ A ⊢ B) >>= λ x → return (r◇□ x)
    check-r◇□ _ = ∅

    -- rules for residuation and monotonicity for (₀ , ⁰)
    check-m⁰ : (J : Sequent) → Mon (LG J)
    check-m⁰ (A ⁰ ⊢ B ⁰) = reset (B ⊢ A) >>= λ x → return (m⁰ x)
    check-m⁰ _ = ∅

    check-m₀ : (J : Sequent) → Mon (LG J)
    check-m₀ (₀ A ⊢ ₀ B) = reset (B ⊢ A) >>= λ x → return (m₀ x)
    check-m₀ _ = ∅

    check-r⁰₀ : (J : Sequent) → Mon (LG J)
    check-r⁰₀ (A ⊢ ₀ B) = continue (B ⊢ A ⁰) >>= λ x → return (r⁰₀ x)
    check-r⁰₀ _ = ∅

    check-r₀⁰ : (J : Sequent) → Mon (LG J)
    check-r₀⁰ (A ⊢ B ⁰) = continue (B ⊢ ₀ A) >>= λ x → return (r₀⁰ x)
    check-r₀⁰ _ = ∅

    -- rules for residuation and monotonicity for (₁ , ¹)
    check-m₁ : (J : Sequent) → Mon (LG J)
    check-m₁ (₁ A ⊢ ₁ B) = reset (B ⊢ A) >>= λ x → return (m₁ x)
    check-m₁ _ = ∅

    check-m¹ : (J : Sequent) → Mon (LG J)
    check-m¹ ( A ¹ ⊢ B ¹) = reset (B ⊢ A) >>= λ x → return (m¹ x)
    check-m¹ _ = ∅

    check-r¹₁ : (J : Sequent) → Mon (LG J)
    check-r¹₁ (₁ A ⊢ B) = continue (B ¹ ⊢ A) >>= λ x → return (r¹₁ x)
    check-r¹₁ _ = ∅

    check-r₁¹ : (J : Sequent) → Mon (LG J)
    check-r₁¹ (A ¹ ⊢ B) = continue (₁ B ⊢ A) >>= λ x → return (r₁¹ x)
    check-r₁¹ _ = ∅

    -- rules for residuation and monotonicity for (⇐ , ⊗ , ⇒)
    check-m⊗ : (J : Sequent) → Mon (LG J)
    check-m⊗ (A ⊗ C ⊢ B ⊗ D) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⊗ x y)
    check-m⊗ _ = ∅

    check-m⇒ : (J : Sequent) → Mon (LG J)
    check-m⇒ (B ⇒ C ⊢ A ⇒ D) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⇒ x y)
    check-m⇒ _ = ∅

    check-m⇐ : (J : Sequent) → Mon (LG J)
    check-m⇐ (A ⇐ D ⊢ B ⇐ C) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⇐ x y)
    check-m⇐ _ = ∅

    check-r⇒⊗ : (J : Sequent) → Mon (LG J)
    check-r⇒⊗ (A ⊗ B ⊢ C) = continue (B ⊢ A ⇒ C) >>= λ x → return (r⇒⊗ x)
    check-r⇒⊗ _  = ∅

    check-r⇐⊗ : (J : Sequent) → Mon (LG J)
    check-r⇐⊗ (A ⊗ B ⊢ C) = continue (A ⊢ C ⇐ B) >>= λ x → return (r⇐⊗ x)
    check-r⇐⊗ _  = ∅

    check-r⊗⇒ : (J : Sequent) → Mon (LG J)
    check-r⊗⇒ (B ⊢ A ⇒ C) = continue (A ⊗ B ⊢ C) >>= λ x → return (r⊗⇒ x)
    check-r⊗⇒ _  = ∅

    check-r⊗⇐ : (J : Sequent) → Mon (LG J)
    check-r⊗⇐ (A ⊢ C ⇐ B) = continue (A ⊗ B ⊢ C) >>= λ x → return (r⊗⇐ x)
    check-r⊗⇐ _  = ∅

    -- rules for residuation and monotonicity for (⇚ , ⊕ , ⇛)
    check-m⊕ : (J : Sequent) → Mon (LG J)
    check-m⊕ (A ⊕ C ⊢ B ⊕ D) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⊕ x y)
    check-m⊕ _ = ∅

    check-m⇚ : (J : Sequent) → Mon (LG J)
    check-m⇚ (A ⇚ D ⊢ B ⇚ C) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⇚ x y)
    check-m⇚ _ = ∅

    check-m⇛ : (J : Sequent) → Mon (LG J)
    check-m⇛ (D ⇛ A ⊢ C ⇛ B) =
      reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⇛ y x)
    check-m⇛ _ = ∅

    check-r⇚⊕ : (J : Sequent) → Mon (LG J)
    check-r⇚⊕ (C ⊢ B ⊕ A) = continue (C ⇚ A ⊢ B) >>= λ x → return (r⇚⊕ x)
    check-r⇚⊕ _  = ∅

    check-r⊕⇚ : (J : Sequent) → Mon (LG J)
    check-r⊕⇚ (C ⇚ A ⊢ B) = continue (C ⊢ B ⊕ A) >>= λ x → return (r⊕⇚ x)
    check-r⊕⇚ _  = ∅

    check-r⇛⊕ : (J : Sequent) → Mon (LG J)
    check-r⇛⊕ (C ⊢ B ⊕ A) = continue (B ⇛ C ⊢ A) >>= λ x → return (r⇛⊕ x)
    check-r⇛⊕ _  = ∅

    check-r⊕⇛ : (J : Sequent) → Mon (LG J)
    check-r⊕⇛ (B ⇛ C ⊢ A) = continue (C ⊢ B ⊕ A) >>= λ x → return (r⊕⇛ x)
    check-r⊕⇛ _  = ∅

    -- grishin distributives
    check-d⇛⇐ : (J : Sequent) → Mon (LG J)
    check-d⇛⇐ (C ⇛ A ⊢ D ⇐ B) = reset (A ⊗ B ⊢ C ⊕ D) >>= λ x → return (d⇛⇐ x)
    check-d⇛⇐ _ = ∅

    check-d⇛⇒ : (J : Sequent) → Mon (LG J)
    check-d⇛⇒ (C ⇛ B ⊢ A ⇒ D) = reset (A ⊗ B ⊢ C ⊕ D) >>= λ x → return (d⇛⇒ x)
    check-d⇛⇒ _ = ∅

    check-d⇚⇒ : (J : Sequent) → Mon (LG J)
    check-d⇚⇒ (B ⇚ D ⊢ A ⇒ C) = reset (A ⊗ B ⊢ C ⊕ D) >>= λ x → return (d⇚⇒ x)
    check-d⇚⇒ _ = ∅

    check-d⇚⇐ : (J : Sequent) → Mon (LG J)
    check-d⇚⇐ (A ⇚ D ⊢ C ⇐ B) = reset (A ⊗ B ⊢ C ⊕ D) >>= λ x → return (d⇚⇐ x)
    check-d⇚⇐ _ = ∅



findMaybe : (J : Sequent) → Maybe (LG J)
findMaybe = search Data.Maybe.monadPlus

find : (J : Sequent) → From-just (LG J) (findMaybe J)
find J = from-just (findMaybe J)

findAll : (J : Sequent) → List (LG J)
findAll = search Data.List.monadPlus
