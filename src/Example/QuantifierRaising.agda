open import Data.Bool                             using (Bool; true; false)
open import Data.Nat                              using (suc; zero) renaming (ℕ to Entity)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Example.QuantifierRaising where


open import Example.Base
open import Logic.Classical.Ordered.LambdaCMinus.Base Univ as λC⁻


