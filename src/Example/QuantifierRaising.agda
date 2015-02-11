------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function
open import Data.Bool                             using (Bool; true; false; _∧_)
open import Data.Fin                              using (Fin; suc; zero; #_; toℕ)
open import Data.List                             using (List; map; foldr; _++_) renaming ([] to ∅; _∷_ to _,_)
open import Data.Nat                              using (ℕ; suc; zero)
open import Data.Product                          using (_,_)
open import Data.String                           using (String)
open import Data.Vec                              using (Vec; _∷_; [])
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Example.Lexicon

module Example.QuantifierRaising where

EVERY : Type
EVERY = el NP - (el S - el S) ⇐ el N
every : ⟦ EVERY ⟧ᵀ
every = λ k p → forallₑ (λ x → k ((λ {(k , b) → k (p x ∧ b)}) , x))

SOME : Type
SOME = el NP - (el S - el S) ⇐ el N
some : ⟦ SOME ⟧ᵀ
some = λ k p → existsₑ (λ x → k ((λ {(k , b) → k (p x ∧ b)}) , x))

EVERYONE : Type
EVERYONE = EVERY ⊗ PERSON
everyone : ⟦ EVERYONE ⟧ᵀ
everyone = λ k → k (every , person)

SOMEONE : Type
SOMEONE = SOME ⊗ PERSON
someone : ⟦ SOMEONE ⟧ᵀ
someone = λ k → k (some , person)

JOHN_LOVES_MARY : λC⁻ · JOHN · ⊗ (· LOVES · ⊗ · MARY ·) ⊢[ el S ] ∅
JOHN_LOVES_MARY = ⇒ₑ ax (⇐ₑ ax ax)
john_loves_mary : Bool
john_loves_mary = [ JOHN_LOVES_MARY ] (john , (loves , (mary , ∅))) (id , ∅)

MARY_LOVES_EVERYONE : λC⁻ · MARY · ⊗ (· LOVES · ⊗ · EVERYONE ·) ⊢[ el S ] ∅
MARY_LOVES_EVERYONE = A-Aᵢ
                    $      ⇒ₑ ax
                    $ flip ⇐ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
                    $ ⇐ᵢ
                    $ flip ⇐ₑ (-ₑ₀ (# 0) ax)
                    $ ax

mary_loves_everyone : Bool
mary_loves_everyone = [ MARY_LOVES_EVERYONE ] (mary , (loves , (everyone , ∅))) (id , ∅)

EVERYONE_LOVES_MARY : λC⁻ · EVERYONE · ⊗ (· LOVES · ⊗ · MARY ·) ⊢[ el S ] ∅
EVERYONE_LOVES_MARY = A-Aᵢ
                    $      ⇒ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
                    $      ⇒ᵢ
                    $      ⇒ₑ (-ₑ₀ (# 0) ax)
                    $ flip ⇐ₑ ax
                    $ ax

everyone_loves_mary : Bool
everyone_loves_mary = [ EVERYONE_LOVES_MARY ] (everyone , (loves , (mary , ∅))) (id , ∅)


EVERYONE_LOVES_SOMEONEˢ : λC⁻ · EVERYONE · ⊗ (· LOVES · ⊗ · SOMEONE ·) ⊢[ el S ] ∅
EVERYONE_LOVES_SOMEONEˢ
  = A-Aᵢ
  $      ⇒ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
  $      ⇒ᵢ
  $      ⇒ₑ (-ₑ₀ (# 0) ax)
  $ flip ⇐ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
  $      ⇐ᵢ
  $ flip ⇐ₑ (-ₑ₀ (# 0) ax)
  $ ax

everyone_loves_someoneˢ : Bool
everyone_loves_someoneˢ = [ EVERYONE_LOVES_SOMEONEˢ ] (everyone , (loves , (someone , ∅))) (id , ∅)

̈everyone_loves_someoneˢ̈  : String
̈everyone_loves_someoneˢ̈  =
  showTermWith ("everyone" ∷ ("loves" ∷ ("someone" ∷ []))) [] [ EVERYONE_LOVES_SOMEONEˢ ]ˣ

{-
C⁻(λ k0 → k0 (
  let (x0 , k1) =
    C⁻(λ k2 → k0 (
      (λ x1 →
        (
          (
            (λ x2 → (loves (let (x3 , k3) = x2 in x3)))   <- lose k3
            (case someone of (x4 , x5) → (x4 x5))
          )
          (let (x6 , k4) = x1 in x6)                      <- lose k4
        )
      )
      (case everyone of (x7 , x8) → (x7 x8))
    ))
  in x0
  ))
-}


EVERYONE_LOVES_SOMEONEⁱ : λC⁻ · EVERYONE · ⊗ (· LOVES · ⊗ · SOMEONE ·) ⊢[ el S ] ∅
EVERYONE_LOVES_SOMEONEⁱ
  = A-Aᵢ
  $      ⇒ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
  $ flip ⇐ₑ (⊗ₑ [] ax (⇐ₑ ax ax))
  $      ⇐ᵢ
  $      ⇒ᵢ
  $      ⇒ₑ (-ₑ₀ (# 0) ax)
  $ flip ⇐ₑ (-ₑ₀ (# 0) ax)
  $ ax

everyone_loves_someoneⁱ : Bool
everyone_loves_someoneⁱ = [ EVERYONE_LOVES_SOMEONEⁱ ] (everyone , (loves , (someone , ∅))) (id , ∅)

s = {!̈everyone_loves_someoneˢ̈ !}
