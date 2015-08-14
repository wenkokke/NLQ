------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Category.Monad             using (module RawMonadPlus; RawMonadPlus)
open import Data.Maybe                 using (Maybe; From-just; from-just)
open import Data.List                  using (List; _∷_; [])
open import Data.List.Any              using (any)
open import Data.Product               using (_×_; _,_; proj₁; proj₂)
open import Function                   using (_∘_)
open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Nullary.Decidable using (fromWitness)
open import Relation.Binary.PropositionalEquality as P
open import Logic.Polarity


module Logic.LG.Pol.ProofSearch
  {ℓ} (Atom : Set ℓ)
      (Polarityᴬ? : Atom → Polarity)
      (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B))
      where


open import Logic.LG.Type.Polarised      Atom Polarityᴬ?
open import Logic.LG.Type                Atom as T
open import Logic.LG.Structure.Polarised Atom
open import Logic.LG.Judgement           Atom as J
open import Logic.LG.Pol.Base         Atom Polarityᴬ?

open T.DecEq _≟-Atom_ using (_≟-Type_)
open J.DecEq _≟-Atom_ using (_≟-Judgement_)


{-# TERMINATING #-}
search : {Mon : Set ℓ → Set ℓ} (monadPlus : RawMonadPlus Mon) (J : Judgement) → Mon (fLG J)
search {Mon} monadPlus = search′ []
  where
  open RawMonadPlus monadPlus using (∅; _∣_; return; _>>=_)

  search′ : (seen : List Judgement) (J : Judgement) → Mon (fLG J)
  search′ seen J with any (J ≟-Judgement_) seen
  search′ seen J | yes J∈seen = ∅
  search′ seen J | no  J∉seen
    = check-ax⁺ J ∣ check-ax⁻ J
    ∣ check-⇁   J ∣ check-↽   J ∣ check-⇀   J ∣ check-↼   J
    ∣ check-◇ᴸ  J
    ∣ check-◇ᴿ  J
    ∣ check-□ᴸ  J
    ∣ check-□ᴿ  J
    ∣ check-r□◇ J
    ∣ check-r◇□ J
    ∣ check-₀ᴸ  J ∣ check-₀ᴿ  J ∣ check-⁰ᴸ  J ∣ check-⁰ᴿ  J ∣ check-r⁰₀ J ∣ check-r₀⁰ J
    ∣ check-₁ᴸ  J ∣ check-₁ᴿ  J ∣ check-¹ᴸ  J ∣ check-¹ᴿ  J ∣ check-r¹₁ J ∣ check-r₁¹ J
    ∣ check-⊗ᴸ  J ∣ check-⊗ᴿ  J ∣ check-⇒ᴸ  J ∣ check-⇒ᴿ  J ∣ check-⇐ᴸ  J ∣ check-⇐ᴿ  J
    ∣ check-r⇒⊗ J ∣ check-r⊗⇒ J ∣ check-r⇐⊗ J ∣ check-r⊗⇐ J
    ∣ check-⊕ᴸ  J ∣ check-⊕ᴿ  J ∣ check-⇚ᴸ  J ∣ check-⇚ᴿ  J ∣ check-⇛ᴸ  J ∣ check-⇛ᴿ  J
    ∣ check-r⇚⊕ J ∣ check-r⊕⇚ J ∣ check-r⇛⊕ J ∣ check-r⊕⇛ J
    ∣ check-d⇛⇐ J ∣ check-d⇛⇒ J ∣ check-d⇚⇒ J ∣ check-d⇚⇐ J
    where
    reset    = search′ []         -- for rules which make progress
    continue = search′ (J ∷ seen) -- for rules which make no progress

    check-ax⁺ : (J : Judgement) → Mon (fLG J)
    check-ax⁺ (· A · ⊢[ B ])  with A ≟-Type B | Positive? B
    ...  | yes A=B | yes _ rewrite A=B = return ax⁺
    ...  | _       |     _             = ∅
    check-ax⁺            _             = ∅
    check-ax⁻ : (J : Judgement) → Mon (fLG J)
    check-ax⁻ ([ A ]⊢ · B ·)  with A ≟-Type B | Negative? A
    ... | yes A=B | yes _ rewrite A=B = return ax⁻
    ... | _       |     _             = ∅
    check-ax⁻           _             = ∅

    check-⇁   : (J : Judgement) → Mon (fLG J)
    check-⇁   (X ⊢[ B ]) with Negative? B
    ... | yes B⁻ = continue (X ⊢ · B ·) >>= λ x → return (⇁ {p = fromWitness B⁻} x)
    ... | no  B⁺ = ∅
    check-⇁   _  = ∅
    check-↽   : (J : Judgement) → Mon (fLG J)
    check-↽   ([ A ]⊢ Y) with Positive? A
    ... | yes A⁺ = continue (· A · ⊢ Y) >>= λ x → return (↽ {p = fromWitness A⁺} x)
    ... | no  A⁻ = ∅
    check-↽   _  = ∅
    check-⇀   : (J : Judgement) → Mon (fLG J)
    check-⇀   (X ⊢ · B ·) with Positive? B
    ... | yes B⁺ = continue (X ⊢[ B ]) >>= λ x → return (⇀ {p = fromWitness B⁺} x)
    ... | no  B⁻ = ∅
    check-⇀   _  = ∅
    check-↼   : (J : Judgement) → Mon (fLG J)
    check-↼   (· A · ⊢ Y) with Negative? A
    ... | yes A⁻ = continue ([ A ]⊢ Y) >>= λ x → return (↼ {p = fromWitness A⁻} x)
    ... | no  A⁺ = ∅
    check-↼   _  = ∅

    check-◇ᴸ  : (J : Judgement) → Mon (fLG J)
    check-◇ᴸ  (· ◇ A · ⊢ Y)      = continue (⟨ · A · ⟩ ⊢ Y) >>= λ x → return (◇ᴸ x)
    check-◇ᴸ  _ = ∅
    check-◇ᴿ  : (J : Judgement) → Mon (fLG J)
    check-◇ᴿ  (⟨ X ⟩ ⊢[ ◇ B ])   = continue (X ⊢[ B ]) >>= λ x → return (◇ᴿ x)
    check-◇ᴿ  _ = ∅
    check-□ᴸ  : (J : Judgement) → Mon (fLG J)
    check-□ᴸ  ([ □ A ]⊢ [ Y ])   = continue ([ A ]⊢ Y) >>= λ x → return (□ᴸ x)
    check-□ᴸ  _ = ∅
    check-□ᴿ  : (J : Judgement) → Mon (fLG J)
    check-□ᴿ  (X ⊢ · □ B ·)      = continue (X ⊢ [ · B · ]) >>= λ x → return (□ᴿ x)
    check-□ᴿ  _ = ∅
    check-r□◇ : (J : Judgement) → Mon (fLG J)
    check-r□◇ (⟨ X ⟩ ⊢ Y)        = continue (X ⊢ [ Y ]) >>= λ x → return (r□◇ x)
    check-r□◇ _ = ∅
    check-r◇□ : (J : Judgement) → Mon (fLG J)
    check-r◇□ (X ⊢ [ Y ])        = continue (⟨ X ⟩ ⊢ Y) >>= λ x → return (r◇□ x)
    check-r◇□ _ = ∅

    check-₀ᴸ  : (J : Judgement) → Mon (fLG J)
    check-₀ᴸ  ([ ₀ A ]⊢ ₀ Y)     = continue (Y ⊢[ A ]) >>= λ x → return (₀ᴸ x)
    check-₀ᴸ  _ = ∅
    check-₀ᴿ  : (J : Judgement) → Mon (fLG J)
    check-₀ᴿ  (X ⊢ · ₀ B ·)      = continue (X ⊢ ₀ · B ·) >>= λ x → return (₀ᴿ x)
    check-₀ᴿ  _ = ∅
    check-⁰ᴸ  : (J : Judgement) → Mon (fLG J)
    check-⁰ᴸ  ([ A ⁰ ]⊢ Y ⁰)     = continue (Y ⊢[ A ]) >>= λ x → return (⁰ᴸ x)
    check-⁰ᴸ  _ = ∅
    check-⁰ᴿ  : (J : Judgement) → Mon (fLG J)
    check-⁰ᴿ  (X ⊢ · B ⁰ ·)      = continue (X ⊢ · B · ⁰) >>= λ x → return (⁰ᴿ x)
    check-⁰ᴿ  _ = ∅
    check-r⁰₀ : (J : Judgement) → Mon (fLG J)
    check-r⁰₀ (X ⊢ ₀ Y)          = continue (Y ⊢ X ⁰) >>= λ x → return (r⁰₀ x)
    check-r⁰₀ _ = ∅
    check-r₀⁰ : (J : Judgement) → Mon (fLG J)
    check-r₀⁰ (X ⊢ Y ⁰)          = continue (Y ⊢ ₀ X) >>= λ x → return (r₀⁰ x)
    check-r₀⁰ _ = ∅

    check-₁ᴸ  : (J : Judgement) → Mon (fLG J)
    check-₁ᴸ  (· ₁ A · ⊢ Y)      = continue (₁ · A · ⊢ Y) >>= λ x → return (₁ᴸ x)
    check-₁ᴸ  _ = ∅
    check-₁ᴿ  : (J : Judgement) → Mon (fLG J)
    check-₁ᴿ  (₁ X ⊢[ ₁ B ])     = continue ([ B ]⊢ X) >>= λ x → return (₁ᴿ x)
    check-₁ᴿ  _ = ∅
    check-¹ᴸ  : (J : Judgement) → Mon (fLG J)
    check-¹ᴸ  (· A ¹ · ⊢ Y)      = continue (· A · ¹ ⊢ Y) >>= λ x → return (¹ᴸ x)
    check-¹ᴸ  _ = ∅
    check-¹ᴿ  : (J : Judgement) → Mon (fLG J)
    check-¹ᴿ  (X ¹ ⊢[ B ¹ ])     = continue ([ B ]⊢ X) >>= λ x → return (¹ᴿ x)
    check-¹ᴿ  _ = ∅
    check-r¹₁ : (J : Judgement) → Mon (fLG J)
    check-r¹₁ (₁ X ⊢ Y)          = continue (Y ¹ ⊢ X) >>= λ x → return (r¹₁ x)
    check-r¹₁ _ = ∅
    check-r₁¹ : (J : Judgement) → Mon (fLG J)
    check-r₁¹ (X ¹ ⊢ Y)          = continue (₁ Y ⊢ X) >>= λ x → return (r₁¹ x)
    check-r₁¹ _ = ∅

    check-⊗ᴸ  : (J : Judgement) → Mon (fLG J)
    check-⊗ᴸ  (· A ⊗ B · ⊢ Y)    = continue (· A · ⊗ · B · ⊢ Y) >>= λ x → return (⊗ᴸ x)
    check-⊗ᴸ  _ = ∅
    check-⊗ᴿ  : (J : Judgement) → Mon (fLG J)
    check-⊗ᴿ  (X ⊗ Y ⊢[ A ⊗ B ]) =
      reset (X ⊢[ A ]) >>= λ x → reset (Y ⊢[ B ]) >>= λ y → return (⊗ᴿ x y)
    check-⊗ᴿ  _ = ∅
    check-⇒ᴸ  : (J : Judgement) → Mon (fLG J)
    check-⇒ᴸ  ([ A ⇒ B ]⊢ X ⇒ Y) =
      reset (X ⊢[ A ]) >>= λ x → reset ([ B ]⊢ Y) >>= λ y → return (⇒ᴸ x y)
    check-⇒ᴸ  _ = ∅
    check-⇒ᴿ  : (J : Judgement) → Mon (fLG J)
    check-⇒ᴿ  (X ⊢ · A ⇒ B ·)    = continue (X ⊢ · A · ⇒ · B ·) >>= λ x → return (⇒ᴿ x)
    check-⇒ᴿ  _ = ∅
    check-⇐ᴸ  : (J : Judgement) → Mon (fLG J)
    check-⇐ᴸ  ([ B ⇐ A ]⊢ Y ⇐ X) =
      reset (X ⊢[ A ]) >>= λ x → reset ([ B ]⊢ Y) >>= λ y → return (⇐ᴸ x y)
    check-⇐ᴸ  _ = ∅
    check-⇐ᴿ  : (J : Judgement) → Mon (fLG J)
    check-⇐ᴿ  (X ⊢ · B ⇐ A ·)    = continue (X ⊢ · B · ⇐ · A ·) >>= λ x → return (⇐ᴿ x)
    check-⇐ᴿ  _ = ∅

    check-r⇒⊗ : (J : Judgement) → Mon (fLG J)
    check-r⇒⊗ (X ⊗ Y ⊢ Z)        = continue (Y ⊢ X ⇒ Z) >>= λ x → return (r⇒⊗ x)
    check-r⇒⊗ _ = ∅
    check-r⊗⇒ : (J : Judgement) → Mon (fLG J)
    check-r⊗⇒ (Y ⊢ X ⇒ Z)        = continue (X ⊗ Y ⊢ Z) >>= λ x → return (r⊗⇒ x)
    check-r⊗⇒ _ = ∅
    check-r⇐⊗ : (J : Judgement) → Mon (fLG J)
    check-r⇐⊗ (X ⊗ Y ⊢ Z)        = continue (X ⊢ Z ⇐ Y) >>= λ x → return (r⇐⊗ x)
    check-r⇐⊗ _ = ∅
    check-r⊗⇐ : (J : Judgement) → Mon (fLG J)
    check-r⊗⇐ (X ⊢ Z ⇐ Y)        = continue (X ⊗ Y ⊢ Z) >>= λ x → return (r⊗⇐ x)
    check-r⊗⇐ _ = ∅

    check-⊕ᴸ  : (J : Judgement) → Mon (fLG J)
    check-⊕ᴸ  ([ B ⊕ A ]⊢ Y ⊕ X) =
      reset ([ B ]⊢ Y) >>= λ x → reset ([ A ]⊢ X) >>= λ y → return (⊕ᴸ x y)
    check-⊕ᴸ  _ = ∅
    check-⊕ᴿ  : (J : Judgement) → Mon (fLG J)
    check-⊕ᴿ  (X ⊢ · B ⊕ A ·)    = continue (X ⊢ · B · ⊕ · A ·) >>= λ x → return (⊕ᴿ x)
    check-⊕ᴿ  _ = ∅
    check-⇚ᴸ  : (J : Judgement) → Mon (fLG J)
    check-⇚ᴸ  (· A ⇚ B · ⊢ X)    = continue (· A · ⇚ · B · ⊢ X) >>= λ x → return (⇚ᴸ x)
    check-⇚ᴸ  _ = ∅
    check-⇚ᴿ  : (J : Judgement) → Mon (fLG J)
    check-⇚ᴿ  (X ⇚ Y ⊢[ A ⇚ B ]) =
      reset (X ⊢[ A ]) >>= λ x → reset ([ B ]⊢ Y) >>= λ y → return (⇚ᴿ x y)
    check-⇚ᴿ  _ = ∅
    check-⇛ᴸ  : (J : Judgement) → Mon (fLG J)
    check-⇛ᴸ  (· B ⇛ A · ⊢ X)    = continue (· B · ⇛ · A · ⊢ X) >>= λ x → return (⇛ᴸ x)
    check-⇛ᴸ  _ = ∅
    check-⇛ᴿ  : (J : Judgement) → Mon (fLG J)
    check-⇛ᴿ  (Y ⇛ X ⊢[ B ⇛ A ]) =
      reset (X ⊢[ A ]) >>= λ x → reset ([ B ]⊢ Y) >>= λ y → return (⇛ᴿ x y)
    check-⇛ᴿ  _ = ∅

    check-r⇚⊕ : (J : Judgement) → Mon (fLG J)
    check-r⇚⊕ (Z ⊢ Y ⊕ X)        = continue (Z ⇚ X ⊢ Y) >>= λ x → return (r⇚⊕ x)
    check-r⇚⊕ _ = ∅
    check-r⊕⇚ : (J : Judgement) → Mon (fLG J)
    check-r⊕⇚ (Z ⇚ X ⊢ Y)        = continue (Z ⊢ Y ⊕ X) >>= λ x → return (r⊕⇚ x)
    check-r⊕⇚ _ = ∅
    check-r⇛⊕ : (J : Judgement) → Mon (fLG J)
    check-r⇛⊕ (Z ⊢ Y ⊕ X)        = continue (Y ⇛ Z ⊢ X) >>= λ x → return (r⇛⊕ x)
    check-r⇛⊕ _ = ∅
    check-r⊕⇛ : (J : Judgement) → Mon (fLG J)
    check-r⊕⇛ (Y ⇛ Z ⊢ X)        = continue (Z ⊢ Y ⊕ X) >>= λ x → return (r⊕⇛ x)
    check-r⊕⇛ _ = ∅

    check-d⇛⇐ : (J : Judgement) → Mon (fLG J)
    check-d⇛⇐ (Z ⇛ X ⊢ W ⇐ Y)    = continue (X ⊗ Y ⊢ Z ⊕ W) >>= λ x → return (d⇛⇐ x)
    check-d⇛⇐ _ = ∅
    check-d⇛⇒ : (J : Judgement) → Mon (fLG J)
    check-d⇛⇒ (Z ⇛ Y ⊢ X ⇒ W)    = continue (X ⊗ Y ⊢ Z ⊕ W) >>= λ x → return (d⇛⇒ x)
    check-d⇛⇒ _ = ∅
    check-d⇚⇒ : (J : Judgement) → Mon (fLG J)
    check-d⇚⇒ (Y ⇚ W ⊢ X ⇒ Z)    = continue (X ⊗ Y ⊢ Z ⊕ W) >>= λ x → return (d⇚⇒ x)
    check-d⇚⇒ _ = ∅
    check-d⇚⇐ : (J : Judgement) → Mon (fLG J)
    check-d⇚⇐ (X ⇚ W ⊢ Z ⇐ Y)    = continue (X ⊗ Y ⊢ Z ⊕ W) >>= λ x → return (d⇚⇐ x)
    check-d⇚⇐ _ = ∅


findMaybe : (J : Judgement) → Maybe (fLG J)
findMaybe = search Data.Maybe.monadPlus

find : (J : Judgement) → From-just (fLG J) (findMaybe J)
find J = from-just (findMaybe J)

findAll : (J : Judgement) → List (fLG J)
findAll = search Data.List.monadPlus
