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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Example.Lexicon


module Example.QuantifierRaising1 where


_⊃_ : Bool → Bool → Bool
true  ⊃ true  = true
true  ⊃ false = false
false ⊃ _     = true


EVERY₁ : Type
EVERY₁ = (NP⁺ ⇚ (S⁻ ⇛ S⁻)) ⇐ N⁺
every₁ : ⟦ EVERY₁ ⟧ᵀ
every₁ = λ {(k , p) → forallₑ (λ x → k (x , (λ {(f , k) → k (λ b → p x ⊃ f b)})))}

SOME₁ : Type
SOME₁ = (NP⁺ ⇚ (S⁻ ⇛ S⁻)) ⇐ N⁺
some₁ : ⟦ SOME₁ ⟧ᵀ
some₁ = λ {(k , p) → existsₑ (λ x → k (x , (λ {(f , k) → k (λ b → p x ∧ f b)})))}


EVERYONE₁ : Type
EVERYONE₁ = EVERY₁ ⊗ PERSON
everyone₁ : ⟦ EVERYONE₁ ⟧ᵀ
everyone₁ = every₁ , person

SOMEONE₁ : Type
SOMEONE₁  = SOME₁  ⊗ PERSON
someone₁  : ⟦ SOMEONE₁ ⟧ᵀ
someone₁  = some₁ , person


JOHN_LOVES_BILL : LG · JOHN · ⊗ · LOVES · ⊗ · BILL · ⊢[ S⁻ ]
JOHN_LOVES_BILL = ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))
john_loves_bill : Bool
john_loves_bill = [ JOHN_LOVES_BILL ] (john , loves′ , bill , ∅) id
--> john loves bill

JOHN_LOVES_EVERYONE₁ : LG · JOHN · ⊗ · LOVES · ⊗ · EVERYONE₁ · ⊢[ S⁻ ]
JOHN_LOVES_EVERYONE₁
  = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (⇚ᴸ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇛⊕ (⇀ (flip ⇛ᴿ ax⁻
  ( JOHN_LOVES_BILL
    )))))))))))))))
john_loves_everyone₁ : Bool
john_loves_everyone₁ = [ JOHN_LOVES_EVERYONE₁ ] (john , loves′ , everyone₁ , ∅) id
--> forallₑ (λ x → person x ⊃ (john loves x))

EVERYONE₁_LOVES_BILL : LG · EVERYONE₁ · ⊗ · LOVES · ⊗ · BILL · ⊢[ S⁻ ]
EVERYONE₁_LOVES_BILL
  = ⇁ (r⇐⊗ (    (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (⇚ᴸ (d⇚⇐ (    (    (r⇛⊕ (⇀ (flip ⇛ᴿ ax⁻
  ( JOHN_LOVES_BILL
    )))))))))))))))
everyone₁_loves_bill : Bool
everyone₁_loves_bill = [ EVERYONE₁_LOVES_BILL ] (everyone₁ , loves′ , bill , ∅) id
--> forallₑ (λ x → person x ⊃ (x loves bill))

EVERYONE₁_LOVES_SOMEONE₁₁ : LG · EVERYONE₁ · ⊗ · LOVES · ⊗ · SOMEONE₁ · ⊢[ S⁻ ]
EVERYONE₁_LOVES_SOMEONE₁₁
  = ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇐⊗ (⇚ᴸ (d⇚⇐ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))) ax⁻))))))) ax⁻)))))))))))))))))))))
everyone₁_loves_someone₁₁ : Bool
everyone₁_loves_someone₁₁ = [ EVERYONE₁_LOVES_SOMEONE₁₁ ] (everyone₁ , loves′ , someone₁ , ∅) id
--> forallₑ (λ x → existsₑ (λ y → person x ⊃ (person y ∧ x loves y)))

EVERYONE₁_LOVES_SOMEONE₁₂ : LG · EVERYONE₁ · ⊗ · LOVES · ⊗ · SOMEONE₁ · ⊢[ S⁻ ]
EVERYONE₁_LOVES_SOMEONE₁₂
  = ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (d⇚⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (d⇚⇒ (r⇚⊕ (r⊗⇒ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇒⊗ (d⇚⇒ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))) ax⁻)))))) ax⁻))))))))))))))))))))))
everyone₁_loves_someone₁₂ : Bool
everyone₁_loves_someone₁₂ = [ EVERYONE₁_LOVES_SOMEONE₁₂ ] (everyone₁ , loves′ , someone₁ , ∅) id
--> forallₑ (λ x → existsₑ (λ y → person y ∧ person x ⊃ (x loves y)))

EVERYONE₁_LOVES_SOMEONE₁₃ : LG · EVERYONE₁ · ⊗ · LOVES · ⊗ · SOMEONE₁ · ⊢[ S⁻ ]
EVERYONE₁_LOVES_SOMEONE₁₃
  = ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (d⇚⇐ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))) ax⁻))))))))))))))) ax⁻)))))))))))
everyone₁_loves_someone₁₃ : Bool
everyone₁_loves_someone₁₃ = [ EVERYONE₁_LOVES_SOMEONE₁₃ ] (everyone₁ , loves′ , someone₁ , ∅) id
--> forallₑ (λ x → existsₑ (λ y → person y ∧ person x ⊃ (x loves y)))

EVERYONE₁_LOVES_SOMEONE₁₄ : LG · EVERYONE₁ · ⊗ · LOVES · ⊗ · SOMEONE₁ · ⊢[ S⁻ ]
EVERYONE₁_LOVES_SOMEONE₁₄
  = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (d⇚⇒ (r⇚⊕ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (d⇚⇐ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇒⊗ (d⇚⇒ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))) ax⁻)))))) ax⁻))))))))))))))))))))))
everyone₁_loves_someone₁₄ : Bool
everyone₁_loves_someone₁₄ = [ EVERYONE₁_LOVES_SOMEONE₁₄ ] (everyone₁ , loves′ , someone₁ , ∅) id
--> existsₑ (λ y → forallₑ (λ x → person y ∧ person x ⊃ (x loves y)))

EVERYONE₁_LOVES_SOMEONE₁₅ : LG · EVERYONE₁ · ⊗ · LOVES · ⊗ · SOMEONE₁ · ⊢[ S⁻ ]
EVERYONE₁_LOVES_SOMEONE₁₅
  = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (d⇚⇐ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))) ax⁻)))))))))))) ax⁻))))))))))))))
everyone₁_loves_someone₁₅ : Bool
everyone₁_loves_someone₁₅ = [ EVERYONE₁_LOVES_SOMEONE₁₅ ] (everyone₁ , loves′ , someone₁ , ∅) id
--> existsₑ (λ y → forallₑ (λ x → person x ⊃ (person y ∧ x loves y)))

MARY_THINKS_SOMEONE₁_LEFT₁ : LG · MARY · ⊗ · THINKS · ⊗ · SOMEONE₁ · ⊗ · LEFT · ⊢[ S⁻ ]
MARY_THINKS_SOMEONE₁_LEFT₁
  = ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ
  ( ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (d⇚⇐ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻)))) ax⁻)))))))))))) (⇒ᴸ ax⁺ ax⁻)))))
mary_thinks_someone₁_left₁ : Bool
mary_thinks_someone₁_left₁ = [ MARY_THINKS_SOMEONE₁_LEFT₁ ] (mary , thinks′ , someone₁ , left′ , ∅) id
--> mary thinks (existsₑ (λ x → person x ∧ x left))

MARY_THINKS_SOMEONE₁_LEFT₂ : LG · MARY · ⊗ · THINKS · ⊗ · SOMEONE₁ · ⊗ · LEFT · ⊢[ S⁻ ]
MARY_THINKS_SOMEONE₁_LEFT₂
  = ⇁ (r⇒⊗ (r⇒⊗ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (r⊗⇐ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ
  ( ⇁ (r⇐⊗ (⇚ᴸ (d⇚⇐ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻)))) ax⁻))))))) (⇒ᴸ ax⁺ ax⁻))))))))))))))
mary_thinks_someone₁_left₂ : Bool
mary_thinks_someone₁_left₂ = [ MARY_THINKS_SOMEONE₁_LEFT₂ ] (mary , thinks′ , someone₁ , left′ , ∅) id
--> existsₑ (λ x → mary thinks (person x ∧ x left))

MARY_THINKS_SOMEONE₁_LEFT₃ : LG · MARY · ⊗ · THINKS · ⊗ · SOMEONE₁ · ⊗ · LEFT · ⊢[ S⁻ ]
MARY_THINKS_SOMEONE₁_LEFT₃
  = ⇁ (r⇒⊗ (r⇒⊗ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺
  ( ↽ (⇚ᴸ (d⇚⇐ (r⇚⊕ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇛⊕ (⇀ (⇛ᴿ
  ( ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ
  ( ⇁ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻)))) (⇒ᴸ ax⁺ ax⁻)))))) ax⁻)))))))))))))))))
mary_thinks_someone₁_left₃ : Bool
mary_thinks_someone₁_left₃ = [ MARY_THINKS_SOMEONE₁_LEFT₃ ] (mary , thinks′ , someone₁ , left′ , ∅) id
--> existsₑ (λ x → person x ∧ mary thinks (x left))
