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
open import Logic.LG.Sequent           Atom as J
open import Logic.LG.Pol.Base         Atom Polarityᴬ?

open T.DecEq _≟-Atom_ using (_≟-Type_)
open J.DecEq _≟-Atom_ using (_≟-Sequent_)


{-# TERMINATING #-}
search : {Mon : Set ℓ → Set ℓ} (monadPlus : RawMonadPlus Mon) (J : Sequent) → Mon (fLG J)
search {Mon} monadPlus = search′ []
  where
  open RawMonadPlus monadPlus using (∅; _∣_; return; _>>=_)

  search′ : (seen : List Sequent) (J : Sequent) → Mon (fLG J)
  search′ seen J with any (J ≟-Sequent_) seen
  search′ seen J | yes J∈seen = ∅
  search′ seen J | no  J∉seen
    = check-ax⁺ J ∣ check-ax⁻ J
    ∣ check-⇁   J ∣ check-↽   J ∣ check-⇀   J ∣ check-↼   J
    ∣ check-◇L  J
    ∣ check-◇R  J
    ∣ check-□L  J
    ∣ check-□R  J
    ∣ check-r□◇ J
    ∣ check-r◇□ J
    ∣ check-₀L  J ∣ check-₀R  J ∣ check-⁰L  J ∣ check-⁰R  J ∣ check-r⁰₀ J ∣ check-r₀⁰ J
    ∣ check-₁L  J ∣ check-₁R  J ∣ check-¹L  J ∣ check-¹R  J ∣ check-r¹₁ J ∣ check-r₁¹ J
    ∣ check-⊗L  J ∣ check-⊗R  J ∣ check-⇒L  J ∣ check-⇒R  J ∣ check-⇐L  J ∣ check-⇐R  J
    ∣ check-r⇒⊗ J ∣ check-r⊗⇒ J ∣ check-r⇐⊗ J ∣ check-r⊗⇐ J
    ∣ check-⊕L  J ∣ check-⊕R  J ∣ check-⇚L  J ∣ check-⇚R  J ∣ check-⇛L  J ∣ check-⇛R  J
    ∣ check-r⇚⊕ J ∣ check-r⊕⇚ J ∣ check-r⇛⊕ J ∣ check-r⊕⇛ J
    ∣ check-d⇛⇐ J ∣ check-d⇛⇒ J ∣ check-d⇚⇒ J ∣ check-d⇚⇐ J
    where
    reset    = search′ []         -- for rules which make progress
    continue = search′ (J ∷ seen) -- for rules which make no progress

    check-ax⁺ : (J : Sequent) → Mon (fLG J)
    check-ax⁺ (· A · ⊢[ B ])  with A ≟-Type B | Positive? B
    ...  | yes A=B | yes _ rewrite A=B = return ax⁺
    ...  | _       |     _             = ∅
    check-ax⁺            _             = ∅
    check-ax⁻ : (J : Sequent) → Mon (fLG J)
    check-ax⁻ ([ A ]⊢ · B ·)  with A ≟-Type B | Negative? A
    ... | yes A=B | yes _ rewrite A=B = return ax⁻
    ... | _       |     _             = ∅
    check-ax⁻           _             = ∅

    check-⇁   : (J : Sequent) → Mon (fLG J)
    check-⇁   (X ⊢[ B ]) with Negative? B
    ... | yes B⁻ = continue (X ⊢ · B ·) >>= λ x → return (⇁ {p = fromWitness B⁻} x)
    ... | no  B⁺ = ∅
    check-⇁   _  = ∅
    check-↽   : (J : Sequent) → Mon (fLG J)
    check-↽   ([ A ]⊢ Y) with Positive? A
    ... | yes A⁺ = continue (· A · ⊢ Y) >>= λ x → return (↽ {p = fromWitness A⁺} x)
    ... | no  A⁻ = ∅
    check-↽   _  = ∅
    check-⇀   : (J : Sequent) → Mon (fLG J)
    check-⇀   (X ⊢ · B ·) with Positive? B
    ... | yes B⁺ = continue (X ⊢[ B ]) >>= λ x → return (⇀ {p = fromWitness B⁺} x)
    ... | no  B⁻ = ∅
    check-⇀   _  = ∅
    check-↼   : (J : Sequent) → Mon (fLG J)
    check-↼   (· A · ⊢ Y) with Negative? A
    ... | yes A⁻ = continue ([ A ]⊢ Y) >>= λ x → return (↼ {p = fromWitness A⁻} x)
    ... | no  A⁺ = ∅
    check-↼   _  = ∅

    check-◇L  : (J : Sequent) → Mon (fLG J)
    check-◇L  (· ◇ A · ⊢ Y)      = continue (⟨ · A · ⟩ ⊢ Y) >>= λ x → return (◇L x)
    check-◇L  _ = ∅
    check-◇R  : (J : Sequent) → Mon (fLG J)
    check-◇R  (⟨ X ⟩ ⊢[ ◇ B ])   = continue (X ⊢[ B ]) >>= λ x → return (◇R x)
    check-◇R  _ = ∅
    check-□L  : (J : Sequent) → Mon (fLG J)
    check-□L  ([ □ A ]⊢ [ Y ])   = continue ([ A ]⊢ Y) >>= λ x → return (□L x)
    check-□L  _ = ∅
    check-□R  : (J : Sequent) → Mon (fLG J)
    check-□R  (X ⊢ · □ B ·)      = continue (X ⊢ [ · B · ]) >>= λ x → return (□R x)
    check-□R  _ = ∅
    check-r□◇ : (J : Sequent) → Mon (fLG J)
    check-r□◇ (⟨ X ⟩ ⊢ Y)        = continue (X ⊢ [ Y ]) >>= λ x → return (r□◇ x)
    check-r□◇ _ = ∅
    check-r◇□ : (J : Sequent) → Mon (fLG J)
    check-r◇□ (X ⊢ [ Y ])        = continue (⟨ X ⟩ ⊢ Y) >>= λ x → return (r◇□ x)
    check-r◇□ _ = ∅

    check-₀L  : (J : Sequent) → Mon (fLG J)
    check-₀L  ([ ₀ A ]⊢ ₀ Y)     = continue (Y ⊢[ A ]) >>= λ x → return (₀L x)
    check-₀L  _ = ∅
    check-₀R  : (J : Sequent) → Mon (fLG J)
    check-₀R  (X ⊢ · ₀ B ·)      = continue (X ⊢ ₀ · B ·) >>= λ x → return (₀R x)
    check-₀R  _ = ∅
    check-⁰L  : (J : Sequent) → Mon (fLG J)
    check-⁰L  ([ A ⁰ ]⊢ Y ⁰)     = continue (Y ⊢[ A ]) >>= λ x → return (⁰L x)
    check-⁰L  _ = ∅
    check-⁰R  : (J : Sequent) → Mon (fLG J)
    check-⁰R  (X ⊢ · B ⁰ ·)      = continue (X ⊢ · B · ⁰) >>= λ x → return (⁰R x)
    check-⁰R  _ = ∅
    check-r⁰₀ : (J : Sequent) → Mon (fLG J)
    check-r⁰₀ (X ⊢ ₀ Y)          = continue (Y ⊢ X ⁰) >>= λ x → return (r⁰₀ x)
    check-r⁰₀ _ = ∅
    check-r₀⁰ : (J : Sequent) → Mon (fLG J)
    check-r₀⁰ (X ⊢ Y ⁰)          = continue (Y ⊢ ₀ X) >>= λ x → return (r₀⁰ x)
    check-r₀⁰ _ = ∅

    check-₁L  : (J : Sequent) → Mon (fLG J)
    check-₁L  (· ₁ A · ⊢ Y)      = continue (₁ · A · ⊢ Y) >>= λ x → return (₁L x)
    check-₁L  _ = ∅
    check-₁R  : (J : Sequent) → Mon (fLG J)
    check-₁R  (₁ X ⊢[ ₁ B ])     = continue ([ B ]⊢ X) >>= λ x → return (₁R x)
    check-₁R  _ = ∅
    check-¹L  : (J : Sequent) → Mon (fLG J)
    check-¹L  (· A ¹ · ⊢ Y)      = continue (· A · ¹ ⊢ Y) >>= λ x → return (¹L x)
    check-¹L  _ = ∅
    check-¹R  : (J : Sequent) → Mon (fLG J)
    check-¹R  (X ¹ ⊢[ B ¹ ])     = continue ([ B ]⊢ X) >>= λ x → return (¹R x)
    check-¹R  _ = ∅
    check-r¹₁ : (J : Sequent) → Mon (fLG J)
    check-r¹₁ (₁ X ⊢ Y)          = continue (Y ¹ ⊢ X) >>= λ x → return (r¹₁ x)
    check-r¹₁ _ = ∅
    check-r₁¹ : (J : Sequent) → Mon (fLG J)
    check-r₁¹ (X ¹ ⊢ Y)          = continue (₁ Y ⊢ X) >>= λ x → return (r₁¹ x)
    check-r₁¹ _ = ∅

    check-⊗L  : (J : Sequent) → Mon (fLG J)
    check-⊗L  (· A ⊗ B · ⊢ Y)    = continue (· A · ⊗ · B · ⊢ Y) >>= λ x → return (⊗L x)
    check-⊗L  _ = ∅
    check-⊗R  : (J : Sequent) → Mon (fLG J)
    check-⊗R  (X ⊗ Y ⊢[ A ⊗ B ]) =
      reset (X ⊢[ A ]) >>= λ x → reset (Y ⊢[ B ]) >>= λ y → return (⊗R x y)
    check-⊗R  _ = ∅
    check-⇒L  : (J : Sequent) → Mon (fLG J)
    check-⇒L  ([ A ⇒ B ]⊢ X ⇒ Y) =
      reset (X ⊢[ A ]) >>= λ x → reset ([ B ]⊢ Y) >>= λ y → return (⇒L x y)
    check-⇒L  _ = ∅
    check-⇒R  : (J : Sequent) → Mon (fLG J)
    check-⇒R  (X ⊢ · A ⇒ B ·)    = continue (X ⊢ · A · ⇒ · B ·) >>= λ x → return (⇒R x)
    check-⇒R  _ = ∅
    check-⇐L  : (J : Sequent) → Mon (fLG J)
    check-⇐L  ([ B ⇐ A ]⊢ Y ⇐ X) =
      reset (X ⊢[ A ]) >>= λ x → reset ([ B ]⊢ Y) >>= λ y → return (⇐L x y)
    check-⇐L  _ = ∅
    check-⇐R  : (J : Sequent) → Mon (fLG J)
    check-⇐R  (X ⊢ · B ⇐ A ·)    = continue (X ⊢ · B · ⇐ · A ·) >>= λ x → return (⇐R x)
    check-⇐R  _ = ∅

    check-r⇒⊗ : (J : Sequent) → Mon (fLG J)
    check-r⇒⊗ (X ⊗ Y ⊢ Z)        = continue (Y ⊢ X ⇒ Z) >>= λ x → return (r⇒⊗ x)
    check-r⇒⊗ _ = ∅
    check-r⊗⇒ : (J : Sequent) → Mon (fLG J)
    check-r⊗⇒ (Y ⊢ X ⇒ Z)        = continue (X ⊗ Y ⊢ Z) >>= λ x → return (r⊗⇒ x)
    check-r⊗⇒ _ = ∅
    check-r⇐⊗ : (J : Sequent) → Mon (fLG J)
    check-r⇐⊗ (X ⊗ Y ⊢ Z)        = continue (X ⊢ Z ⇐ Y) >>= λ x → return (r⇐⊗ x)
    check-r⇐⊗ _ = ∅
    check-r⊗⇐ : (J : Sequent) → Mon (fLG J)
    check-r⊗⇐ (X ⊢ Z ⇐ Y)        = continue (X ⊗ Y ⊢ Z) >>= λ x → return (r⊗⇐ x)
    check-r⊗⇐ _ = ∅

    check-⊕L  : (J : Sequent) → Mon (fLG J)
    check-⊕L  ([ B ⊕ A ]⊢ Y ⊕ X) =
      reset ([ B ]⊢ Y) >>= λ x → reset ([ A ]⊢ X) >>= λ y → return (⊕L x y)
    check-⊕L  _ = ∅
    check-⊕R  : (J : Sequent) → Mon (fLG J)
    check-⊕R  (X ⊢ · B ⊕ A ·)    = continue (X ⊢ · B · ⊕ · A ·) >>= λ x → return (⊕R x)
    check-⊕R  _ = ∅
    check-⇚L  : (J : Sequent) → Mon (fLG J)
    check-⇚L  (· A ⇚ B · ⊢ X)    = continue (· A · ⇚ · B · ⊢ X) >>= λ x → return (⇚L x)
    check-⇚L  _ = ∅
    check-⇚R  : (J : Sequent) → Mon (fLG J)
    check-⇚R  (X ⇚ Y ⊢[ A ⇚ B ]) =
      reset (X ⊢[ A ]) >>= λ x → reset ([ B ]⊢ Y) >>= λ y → return (⇚R x y)
    check-⇚R  _ = ∅
    check-⇛L  : (J : Sequent) → Mon (fLG J)
    check-⇛L  (· B ⇛ A · ⊢ X)    = continue (· B · ⇛ · A · ⊢ X) >>= λ x → return (⇛L x)
    check-⇛L  _ = ∅
    check-⇛R  : (J : Sequent) → Mon (fLG J)
    check-⇛R  (Y ⇛ X ⊢[ B ⇛ A ]) =
      reset (X ⊢[ A ]) >>= λ x → reset ([ B ]⊢ Y) >>= λ y → return (⇛R x y)
    check-⇛R  _ = ∅

    check-r⇚⊕ : (J : Sequent) → Mon (fLG J)
    check-r⇚⊕ (Z ⊢ Y ⊕ X)        = continue (Z ⇚ X ⊢ Y) >>= λ x → return (r⇚⊕ x)
    check-r⇚⊕ _ = ∅
    check-r⊕⇚ : (J : Sequent) → Mon (fLG J)
    check-r⊕⇚ (Z ⇚ X ⊢ Y)        = continue (Z ⊢ Y ⊕ X) >>= λ x → return (r⊕⇚ x)
    check-r⊕⇚ _ = ∅
    check-r⇛⊕ : (J : Sequent) → Mon (fLG J)
    check-r⇛⊕ (Z ⊢ Y ⊕ X)        = continue (Y ⇛ Z ⊢ X) >>= λ x → return (r⇛⊕ x)
    check-r⇛⊕ _ = ∅
    check-r⊕⇛ : (J : Sequent) → Mon (fLG J)
    check-r⊕⇛ (Y ⇛ Z ⊢ X)        = continue (Z ⊢ Y ⊕ X) >>= λ x → return (r⊕⇛ x)
    check-r⊕⇛ _ = ∅

    check-d⇛⇐ : (J : Sequent) → Mon (fLG J)
    check-d⇛⇐ (Z ⇛ X ⊢ W ⇐ Y)    = continue (X ⊗ Y ⊢ Z ⊕ W) >>= λ x → return (d⇛⇐ x)
    check-d⇛⇐ _ = ∅
    check-d⇛⇒ : (J : Sequent) → Mon (fLG J)
    check-d⇛⇒ (Z ⇛ Y ⊢ X ⇒ W)    = continue (X ⊗ Y ⊢ Z ⊕ W) >>= λ x → return (d⇛⇒ x)
    check-d⇛⇒ _ = ∅
    check-d⇚⇒ : (J : Sequent) → Mon (fLG J)
    check-d⇚⇒ (Y ⇚ W ⊢ X ⇒ Z)    = continue (X ⊗ Y ⊢ Z ⊕ W) >>= λ x → return (d⇚⇒ x)
    check-d⇚⇒ _ = ∅
    check-d⇚⇐ : (J : Sequent) → Mon (fLG J)
    check-d⇚⇐ (X ⇚ W ⊢ Z ⇐ Y)    = continue (X ⊗ Y ⊢ Z ⊕ W) >>= λ x → return (d⇚⇐ x)
    check-d⇚⇐ _ = ∅


findMaybe : (J : Sequent) → Maybe (fLG J)
findMaybe = search Data.Maybe.monadPlus

find : (J : Sequent) → From-just (fLG J) (findMaybe J)
find J = from-just (findMaybe J)

findAll : (J : Sequent) → List (fLG J)
findAll = search Data.List.monadPlus
