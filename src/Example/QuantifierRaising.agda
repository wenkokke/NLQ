------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function                              using (_$_; _∘_; id; flip)
open import Data.Bool                             using (Bool; true; false; _∧_)
open import Data.Fin                              using (Fin; suc; zero; #_; toℕ)
open import Data.List                             using (List; map; foldr; _++_)
open import Data.Nat                              using (ℕ; suc; zero)
open import Data.Product                          using (_,_)
open import Data.String                           using (String)
open import Data.Vec                              using (Vec; _∷_; [])
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Example.Lexicon


module Example.QuantifierRaising where


_⊃_ : Bool → Bool → Bool
true  ⊃ true  = true
true  ⊃ false = false
false ⊃ _     = true

------------------------------------------------------------------------
-- These quantifier interpretations below are simply *beautiful*, they
-- are exactly what we want. Therefore, I would *love* to be able to
-- find a solution which uses *exactly* these types.
------------------------------------------------------------------------

EVERY : Type
EVERY = (np⁻ ⇚ (np ⇛ np⁻)) ⇐ n
every : ⟦ EVERY ⟧ᵀ
every = λ {(k , p₁) → k (forallₑ , (λ {(p₂ , k) → k (λ x → p₁ x ⊃ p₂ x)}))}

SOME : Type
SOME = (np⁻ ⇚ (np ⇛ np⁻)) ⇐ n
some : ⟦ SOME ⟧ᵀ
some = λ {(k , p₁) → k (existsₑ , (λ {(p₂ , k) → k (λ x → p₁ x ∧ p₂ x)}))}

EVERYONE : Type
EVERYONE = EVERY ⊗ PERSON
everyone : ⟦ EVERYONE ⟧ᵀ
everyone = every , person

SOMEONE : Type
SOMEONE  = SOME ⊗ PERSON
someone  : ⟦ SOMEONE ⟧ᵀ
someone  = some , person

SOME′ : Type
SOME′ = (np ⇚ (s⁻ ⇛ s⁻)) ⇐ n
some′ : ⟦ SOME′ ⟧ᵀ
some′ = λ {(k , p) → existsₑ (λ x → k (x , (λ {(f , k) → k (λ b → p x ∧ f b)})))}

SOMEONE′ : Type
SOMEONE′  = SOME′ ⊗ PERSON
someone′  : ⟦ SOMEONE′ ⟧ᵀ
someone′  = some′ , person

EVERYONE¹ : Type
EVERYONE¹  = ( ₁ np ) ¹
everyone¹  : ⟦ EVERYONE¹ ⟧ᵀ
everyone¹  = λ p → forallₑ (λ x → person x ⊃ p x)

SOMEONE¹ : Type
SOMEONE¹  = ( ₁ np ) ¹
someone¹  : ⟦ SOMEONE¹ ⟧ᵀ
someone¹  = λ p → existsₑ (λ x → person x ∧ p x)

JOHN_LOVES_BILL : LG · JOHN · ⊗ · LOVES · ⊗ · BILL · ⊢[ s⁻ ]
JOHN_LOVES_BILL = ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))
john_loves_bill : Bool
john_loves_bill = toAgda JOHN_LOVES_BILL (john , loves′ , bill , ∅) id
--> john loves bill



JOHN_LOVES_EVERYONE : LG · JOHN · ⊗ · LOVES · ⊗ · EVERYONE · ⊢[ s⁻ ]
JOHN_LOVES_EVERYONE
  = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))))))))
john_loves_everyone : Bool
john_loves_everyone = toAgda JOHN_LOVES_EVERYONE (john , loves′ , everyone , ∅) id
--> forallₑ (λ x → person x ⊃ (john loves x))

EVERYONE_LOVES_BILL : LG · EVERYONE · ⊗ · LOVES · ⊗ · BILL · ⊢[ s⁻ ]
EVERYONE_LOVES_BILL
  = ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))))))))
everyone_loves_bill : Bool
everyone_loves_bill = toAgda EVERYONE_LOVES_BILL (everyone , loves′ , bill , ∅) id
--> forallₑ (λ x → person x ⊃ (x loves bill))


EVERYONE_LOVES_SOMEONE₁ : LG · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₁
  = ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))))))))))))))
everyone_loves_someone₁ : Bool
everyone_loves_someone₁ = toAgda EVERYONE_LOVES_SOMEONE₁ (everyone , loves′ , someone , ∅) id
--> forallₑ (λ x → person x ⊃ existsₑ (λ y → person y ∧ x loves y))

EVERYONE_LOVES_SOMEONE₂ : LG · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₂
  = ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))))))))))))
everyone_loves_someone₂ : Bool
everyone_loves_someone₂ = toAgda EVERYONE_LOVES_SOMEONE₂ (everyone , loves′ , someone , ∅) id
--> existsₑ (λ y → person y ∧ forallₑ (λ x → person x ⊃ (x loves y)))

EVERYONE_LOVES_SOMEONE₃ : LG · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₃
  = ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))))))))
everyone_loves_someone₃ : Bool
everyone_loves_someone₃ = toAgda EVERYONE_LOVES_SOMEONE₃ (everyone , loves′ , someone , ∅) id
--> forallₑ (λ x → person x ⊃ existsₑ (λ y → person y ∧ x loves y))

EVERYONE_LOVES_SOMEONE₄ : LG · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₄
  = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))))))))))))))))
everyone_loves_someone₄ : Bool
everyone_loves_someone₄ = toAgda EVERYONE_LOVES_SOMEONE₄ (everyone , loves′ , someone , ∅) id
--> existsₑ (λ y → person y ∧ forallₑ (λ x → person x ⊃ (x loves y)))

EVERYONE_LOVES_SOMEONE₅ : LG · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₅
  = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))))))))))))
everyone_loves_someone₅ : Bool
everyone_loves_someone₅ = toAgda EVERYONE_LOVES_SOMEONE₅ (everyone , loves′ , someone , ∅) id
--> forallₑ (λ x → person x ⊃ existsₑ (λ y → person y ∧ x loves y))

EVERYONE_LOVES_SOMEONE₆ : LG · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( ( np⁻ ⇚ ( np ⇛ np⁻ ) ) ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₆
  = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (r⊕⇚ (r⇛⊕ (⇀ (⇛ᴿ ax⁺
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))))))))))
everyone_loves_someone₆ : Bool
everyone_loves_someone₆ = toAgda EVERYONE_LOVES_SOMEONE₆ (everyone , loves′ , someone , ∅) id
--> existsₑ (λ y → person y ∧ forallₑ (λ x → person x ⊃ (x loves y)))


EVERYONE_LOVES_SOMEONE₇ : LG · ( ₁ np ) ¹ · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( ₁ np ) ¹ · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₇
  = ⇁ (r⇐⊗ (·¹ᴿ (r₁¹ (⇀ (₁·ᴿ
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (·¹ᴿ (r₁¹ (⇀ (₁·ᴿ
  ( ↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))
everyone_loves_someone₇ : Bool
everyone_loves_someone₇ = toAgda EVERYONE_LOVES_SOMEONE₇ (everyone¹ , loves′ , someone¹ , ∅) id
--> forallₑ (λ x → person x ⊃ existsₑ (λ y → person y ∧ x loves y))

EVERYONE_LOVES_SOMEONE₈ : LG · ( ₁ np ) ¹ · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( ₁ np ) ¹ · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₈
  = ⇁ (r⇒⊗ (r⇒⊗ (·¹ᴿ (r₁¹ (⇀ (₁·ᴿ
  ( ↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (·¹ᴿ (r₁¹ (⇀ (₁·ᴿ
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))
everyone_loves_someone₈ : Bool
everyone_loves_someone₈ = toAgda EVERYONE_LOVES_SOMEONE₈ (everyone¹ , loves′ , someone¹ , ∅) id
--> existsₑ (λ y → person y ∧ forallₑ (λ x → person x ⊃ (x loves y)))
