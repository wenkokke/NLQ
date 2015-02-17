------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function                              using (_$_; _∘_; id; flip)
open import Data.Bool                             using (Bool; true; false; _∧_)
open import Data.Fin                              using (Fin; suc; zero; #_; toℕ)
open import Data.List                             using (List; map; foldr; _++_) renaming ([] to ∅; _∷_ to _,_)
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

  EVERY    = (el NP ⇚ (el S ⇛ el S)) ⇐ el N
  SOME     = (el NP ⇚ (el S ⇛ el S)) ⇐ el N
  EVERYONE = EVERY ⊗ PERSON
  SOMEONE  = SOME  ⊗ PERSON

  JOHN_LOVES_BILL : LG JOHN ⊗ LOVES ⊗ BILL ⊢ el S
  JOHN_LOVES_BILL = res-⇒⊗ (res-⇐⊗ ax′)

  JOHN_LOVES_EVERYONE : LG JOHN ⊗ LOVES ⊗ EVERYONE ⊢ el S
  JOHN_LOVES_EVERYONE = res-⇒⊗ (res-⇒⊗ (res-⇐⊗ (mon-⇐ (grish₃ (res-⇚⊕ (grish₃ (res-⇛⊕ (mon-⇛ ax (res-⇒⊗ (res-⇐⊗ ax′))))))) ax)))

  EVERYONE_LOVES_BILL : LG EVERYONE ⊗ LOVES ⊗ BILL ⊢ el S
  EVERYONE_LOVES_BILL
    = res-⇐⊗ (res-⇐⊗ (mon-⇐ (grish₄ (res-⇛⊕ (mon-⇛ ax (res-⇒⊗ (res-⇐⊗ ax′))))) ax))

  EVERYONE_LOVES_SOMEONEⁱ : LG EVERYONE ⊗ LOVES ⊗ SOMEONE ⊢ el S
  EVERYONE_LOVES_SOMEONEⁱ
    = res-⇐⊗ (res-⇐⊗ (       (flip mon-⇐ ax (grish₄ (res-⇛⊕ (       (       (mon-⇛ ax (
      res-⇒⊗ (res-⇒⊗ (res-⇐⊗ (flip mon-⇐ ax (grish₃ (res-⇚⊕ (grish₃ (res-⇛⊕ (mon-⇛ ax (
      res-⇒⊗ (res-⇐⊗ ax′)
      )))))))))
      )))))))))

  EVERYONE_LOVES_SOMEONEˢ : LG EVERYONE ⊗ LOVES ⊗ SOMEONE ⊢ el S
  EVERYONE_LOVES_SOMEONEˢ
    = res-⇒⊗ (res-⇒⊗ (res-⇐⊗ (flip mon-⇐ ax (grish₃ (res-⇚⊕ (grish₃ (res-⇛⊕ (mon-⇛ ax (
      res-⇐⊗ (       (res-⇐⊗ (flip mon-⇐ ax (grish₄ (res-⇛⊕ (       (       (mon-⇛ ax (
      res-⇒⊗ (res-⇐⊗ ax′)
      )))))))))
      )))))))))

module UsingLambdaCMinus where

  open Lexicon.UsingLambdaCMinus public

  -- TODO: right now, I'm putting the `p x ⊃ _` in the NP, which is
  -- wrong, since I couldn't restrict it in this position; I need to put
  -- it in what is now just an identity continuation of type S → S
  EVERY = el NP - (el S - el S) ⇐ el N
  SOME  = el NP - (el S - el S) ⇐ el N

  every : ⟦ EVERY ⟧ᵀ
  every = λ k p → forallₑ (λ x → p x ⊃ k ((λ {(k , b) → k b}) , x))
  some  : ⟦ SOME ⟧ᵀ
  some  = λ k p → existsₑ (λ x → p x ∧ k ((λ {(k , b) → k b}) , x))

  EVERYONE : Type
  EVERYONE = EVERY ⊗ PERSON
  everyone : ⟦ EVERYONE ⟧ᵀ
  everyone = λ k → k (every , person)

  SOMEONE : Type
  SOMEONE = SOME ⊗ PERSON
  someone : ⟦ SOMEONE ⟧ᵀ
  someone = λ k → k (some , person)

  JOHN_LOVES_BILL : λC⁻ · JOHN · ⊗ (· LOVES · ⊗ · BILL ·) ⊢[ el S ] ∅
  JOHN_LOVES_BILL = ⇒ₑ ax (⇐ₑ ax ax)
  john_loves_bill : Bool
  john_loves_bill = [ JOHN_LOVES_BILL ] (john , (loves , (bill , ∅))) (id , ∅)


  BILL_LOVES_EVERYONE : λC⁻ · BILL · ⊗ (· LOVES · ⊗ · EVERYONE ·) ⊢[ el S ] ∅
  BILL_LOVES_EVERYONE
    =      ⇒ₑ ax
    $ flip ⇐ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
    $      ⇐ᵢ
    $      -ₑ₂ ax
    $ flip ⇐ₑ ax
    $      ax

  bill_loves_everyone : Bool
  bill_loves_everyone = [ BILL_LOVES_EVERYONE ] (bill , (loves , (everyone , ∅))) (id , ∅)


  EVERYONE_LOVES_BILL : λC⁻ · EVERYONE · ⊗ (· LOVES · ⊗ · BILL ·) ⊢[ el S ] ∅
  EVERYONE_LOVES_BILL
    =      ⇒ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
    $      ⇒ᵢ
    $      -ₑ₁ ax
    $      ⇒ₑ  ax
    $ flip ⇐ₑ  ax
    $      ax

  everyone_loves_bill : Bool
  everyone_loves_bill = [ EVERYONE_LOVES_BILL ] (everyone , (loves , (bill , ∅))) (id , ∅)


  EVERYONE_LOVES_SOMEONEˢ : λC⁻ · EVERYONE · ⊗ (· LOVES · ⊗ · SOMEONE ·) ⊢[ el S ] ∅
  EVERYONE_LOVES_SOMEONEˢ
    =      ⇒ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
    $      ⇒ᵢ
    $      -ₑ₁ ax
    $      ⇒ₑ  ax
    $ flip ⇐ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
    $      ⇐ᵢ
    $      -ₑ₂ ax
    $ flip ⇐ₑ  ax
    $      ax

  everyone_loves_someoneˢ : Bool
  everyone_loves_someoneˢ = [ EVERYONE_LOVES_SOMEONEˢ ] (everyone , (loves , (someone , ∅))) (id , ∅)

  ‶everyone_loves_someone″ˢ : String
  ‶everyone_loves_someone″ˢ =
    showTermWith ("everyone" ∷ ("loves" ∷ ("someone" ∷ []))) [] [ EVERYONE_LOVES_SOMEONEˢ ]ᴵ

  {-(
    (λ x0 →
      (
        let (x1 , k0) = x0
        in  (
              (
                (λ x2 →
                  (
                    let (x3 , k1) = x2
                    in (loves x3)
                  )
                )
                (case someone of (x4 , x5) → (x4 x5))
              )
              x1
            )
      )
    )
    (case everyone of (x6 , x7) → (x6 x7))
  )-}

  EVERYONE_LOVES_SOMEONEⁱ : λC⁻ · EVERYONE · ⊗ (· LOVES · ⊗ · SOMEONE ·) ⊢[ el S ] ∅
  EVERYONE_LOVES_SOMEONEⁱ
    =      ⇒ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
    $ flip ⇐ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
    $      ⇐ᵢ
    $      ⇒ᵢ
    $      -ₑ₁ ax
    $      ⇒ₑ  ax
    $      -ₑ₂ ax
    $ flip ⇐ₑ  ax
    $      ax

  everyone_loves_someoneⁱ : Bool
  everyone_loves_someoneⁱ = [ EVERYONE_LOVES_SOMEONEⁱ ] (everyone , (loves , (someone , ∅))) (id , ∅)

  ‶everyone_loves_someone″ⁱ : String
  ‶everyone_loves_someone″ⁱ =
    showTermWith ("everyone" ∷ ("loves" ∷ ("someone" ∷ []))) [] [ EVERYONE_LOVES_SOMEONEⁱ ]ᴵ

  {-(
    (
      (λ x0 →
        (λ x1 →
          (
            let (x2 , k0) = x1
            in  (
                  (
                    let (x3 , k1) = x0
                    in (loves x3)
                  )
                  x2
                )
          )
        )
      )
      (case someone of (x4 , x5) → (x4 x5))
    )
    (case everyone of (x6 , x7) → (x6 x7))
  )-}
