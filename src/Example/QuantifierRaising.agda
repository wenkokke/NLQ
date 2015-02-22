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


open import Example.Lexicon as Lexicon
     hiding (module UsingLambdaCMinus; module UsingLambekGrishin)


module Example.QuantifierRaising where


_⊃_ : Bool → Bool → Bool
true  ⊃ true  = true
true  ⊃ false = false
false ⊃ _     = true


module UsingLambekGrishin where

  open Lexicon.UsingLambekGrishin public

  EVERY : Type
  EVERY    = (NP⁺ ⇚ (S⁻ ⇛ S⁻)) ⇐ N⁺
  every    : ⟦ EVERY ⟧ᵀ
  every    = λ {(k , p) → forallₑ (λ x → k (x , (λ {(f , k) → k (λ b → p x ⊃ f b)})))}

  SOME : Type
  SOME     = (NP⁺ ⇚ (S⁻ ⇛ S⁻)) ⇐ N⁺
  some     : ⟦ SOME ⟧ᵀ
  some     = λ {(k , p) → existsₑ (λ x → k (x , (λ {(f , k) → k (λ b → p x ∧ f b)})))}

  EVERYONE : Type
  EVERYONE = EVERY ⊗ PERSON
  everyone : ⟦ EVERYONE ⟧ᵀ
  everyone = every , person

  SOMEONE : Type
  SOMEONE  = SOME  ⊗ PERSON
  someone  : ⟦ SOMEONE ⟧ᵀ
  someone  = some , person


  JOHN_LOVES_BILL : LG · JOHN · ⊗ · LOVES · ⊗ · BILL · ⊢[ S⁻ ]
  JOHN_LOVES_BILL = (⇁(r⇒⊗(r⇐⊗(↼(⇐ᴸ(⇒ᴸ(ax⁺) (ax⁻)) (ax⁺))))))

  john_loves_bill : Bool
  john_loves_bill = [ JOHN_LOVES_BILL ] (john , loves′ , bill , ∅) id
  --> john loves bill

  JOHN_LOVES_EVERYONE : LG · JOHN · ⊗ · LOVES · ⊗ · EVERYONE · ⊢[ S⁻ ]
  JOHN_LOVES_EVERYONE
    = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (flip ⇐ᴸ ax⁺ (↽ (⇚ᴸ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇛⊕ (⇀ (⇛ᴿ ax⁻
    ( JOHN_LOVES_BILL
      )))))))))))))))

  john_loves_everyone : Bool
  john_loves_everyone = [ JOHN_LOVES_EVERYONE ] (john , loves′ , everyone , ∅) id
  --> forallₑ (λ x → person x ⊃ (john loves x))

  EVERYONE_LOVES_BILL : LG · EVERYONE · ⊗ · LOVES · ⊗ · BILL · ⊢[ S⁻ ]
  EVERYONE_LOVES_BILL
    = ⇁ (r⇐⊗ (    (⊗ᴸ (r⇐⊗ (↼ (flip ⇐ᴸ ax⁺ (↽ (⇚ᴸ (d⇚⇐ (    (    (r⇛⊕ (⇀ (⇛ᴿ ax⁻
    ( JOHN_LOVES_BILL
      )))))))))))))))

  everyone_loves_bill : Bool
  everyone_loves_bill = [ EVERYONE_LOVES_BILL ] (everyone , loves′ , bill , ∅) id
  --> forallₑ (λ x → person x ⊃ (x loves bill))

  EVERYONE_LOVES_SOMEONEˢ : LG · EVERYONE · ⊗ · LOVES · ⊗ · SOMEONE · ⊢[ S⁻ ]
  EVERYONE_LOVES_SOMEONEˢ
    = ⇁ (r⇐⊗ (    (⊗ᴸ (r⇐⊗ (↼ (flip ⇐ᴸ ax⁺ (↽ (⇚ᴸ (d⇚⇐ (r⇛⊕ (    (    (⇀ (⇛ᴿ ax⁻
    ( ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (flip ⇐ᴸ ax⁺ (↽ (⇚ᴸ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇛⊕ (⇀ (⇛ᴿ ax⁻
    ( JOHN_LOVES_BILL
      )))))))))))))))
      )))))))))))))))

  everyone_loves_someoneˢ : Bool
  everyone_loves_someoneˢ = [ EVERYONE_LOVES_SOMEONEˢ ] (everyone , loves′ , someone , ∅) id
  --> forallₑ (λ x → existsₑ (λ y → person y ∧ (person x ⊃ (y lovedBy x))))

  EVERYONE_LOVES_SOMEONEⁱ : LG · EVERYONE · ⊗ · LOVES · ⊗ · SOMEONE · ⊢[ S⁻ ]
  EVERYONE_LOVES_SOMEONEⁱ
    = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (flip ⇐ᴸ ax⁺ (↽ (⇚ᴸ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇛⊕ (⇀ (⇛ᴿ ax⁻
    ( ⇁ (r⇐⊗ (    (⊗ᴸ (r⇐⊗ (↼ (flip ⇐ᴸ ax⁺ (↽ (⇚ᴸ (d⇚⇐ (    (    (r⇛⊕ (⇀ (⇛ᴿ ax⁻
    ( JOHN_LOVES_BILL
      )))))))))))))))
      )))))))))))))))

  everyone_loves_someoneⁱ : Bool
  everyone_loves_someoneⁱ = [ EVERYONE_LOVES_SOMEONEⁱ ] (everyone , loves′ , someone , ∅) id
  --> existsₑ (λ x → forallₑ (λ y → person y ⊃ (person x ∧ (x lovedBy y))))

  MARY_THINKS_SOMEONE_LEFT : LG · MARY · ⊗ · THINKS · ⊗ · SOMEONE · ⊗ · LEFT · ⊢[ S⁻ ]
  MARY_THINKS_SOMEONE_LEFT
    = {!!}

  mary_thinks_someone_left : Bool
  mary_thinks_someone_left = [ MARY_THINKS_SOMEONE_LEFT ] (mary , (thinks′ , {!!})) {!!}
