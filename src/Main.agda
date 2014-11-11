------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Data.List using ([])


module Main where


data Univ : Set where
  S  : Univ
  N  : Univ
  NP : Univ


open import Logic.Lambek.Type             Univ as T
open import Logic.Lambek.ResMon.Judgement Univ as RMJ
open import Logic.Lambek.ResMon.Base      Univ as RMB
open import Logic.Lambek.ResMon.Trans     Univ as RMT


data Lexicon : Set where
  EVERYBODY : Lexicon
  FINDS     : Lexicon
  SOME      : Lexicon
  UNICORN   : Lexicon

⟦_⟧ : Lexicon → Type
⟦ EVERYBODY ⟧ = (el NP ⇐ el N) ⊗ el N
⟦ FINDS     ⟧ = (el NP ⇒ el S) ⇐ el NP
⟦ SOME      ⟧ = el NP ⇐ el N
⟦ UNICORN   ⟧ = el N


test₁ : NL ⟦ EVERYBODY ⟧ ⊗ ⟦ FINDS ⟧ ⊗ ⟦ SOME ⟧ ⊗ ⟦ UNICORN ⟧ ⊢ el S
test₁ = res-⇒⊗ (res-⇒⊗  (appl-⇐′ (res-⊗⇒ (appl-⇐′
               (res-⇐⇒′ (appl-⇐′ (res-⊗⇐ (appl-⇒′ id))))))))
