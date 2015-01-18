------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Data.List using ([])


module Main where


data Lexicon : Set where
  EVERYBODY : Lexicon
  FINDS     : Lexicon
  SOME      : Lexicon
  UNICORN   : Lexicon


module TestLambek where

  data Univ : Set where
    S   : Univ
    N   : Univ
    NP  : Univ

  open import Logic.Lambek.Type             Univ as T
  open import Logic.Lambek.ResMon.Judgement Univ as RMJ
  open import Logic.Lambek.ResMon.Base      Univ as RMB
  open import Logic.Lambek.ResMon.Trans     Univ as RMT

  ⟦_⟧ : Lexicon → Type
  ⟦ EVERYBODY ⟧ = (el NP ⇐ el N) ⊗ el N
  ⟦ FINDS     ⟧ = (el NP ⇒ el S) ⇐ el NP
  ⟦ SOME      ⟧ = el NP ⇐ el N
  ⟦ UNICORN   ⟧ = el N

  test₁ : NL ⟦ EVERYBODY ⟧ ⊗ ⟦ FINDS ⟧ ⊗ ⟦ SOME ⟧ ⊗ ⟦ UNICORN ⟧ ⊢ el S
  test₁ = res-⇒⊗ (res-⇒⊗  (appl-⇐′ (res-⊗⇒ (appl-⇐′
                 (res-⇐⇒′ (appl-⇐′ (res-⊗⇐ (appl-⇒′ id))))))))

  test₂ : NL ⟦ EVERYBODY ⟧ ⊗ ⟦ FINDS ⟧ ⊗ ⟦ SOME ⟧ ⊗ ⟦ UNICORN ⟧ ⊢ el S
  test₂ = res-⇐⊗ (appl-⇐′ (res-⇒⇐′ (res-⇒⊗ (appl-⇐′ (res-⇐⇒′ id′) ))))


module TestCMinus where

  data Univ : Set where
    ⫫   : Univ
    S   : Univ
    N   : Univ
    NP  : Univ

  open import Logic.Intuitionistic.Type              Univ   as T renaming (_⇛_ to _-_)
  open import Logic.Intuitionistic.Structure         Univ   as S
  open import Logic.Intuitionistic.CMinus1.Judgement Univ   as CMJ
  open import Logic.Intuitionistic.CMinus1.Base      Univ ⫫ as CMB

  _⇐_ : Type → Type → Type
  B ⇐ A = A ⇒ B

  ⟦_⟧ : Lexicon → Type
  ⟦ EVERYBODY ⟧ = (el NP ⇐ el N) - el N
  ⟦ FINDS     ⟧ = (el NP ⇒ el S) ⇐ el NP
  ⟦ SOME      ⟧ = el NP ⇐ el N
  ⟦ UNICORN   ⟧ = el N

  --test₁ : λC⁻₁ ⟦ EVERYBODY ⟧ ⊗ ⟦ FINDS ⟧ ⊗ ⟦ SOME ⟧ ⊗ ⟦ UNICORN ⟧ ⊢ el S
  --test₁ = ?
