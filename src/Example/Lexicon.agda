------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function
open import Data.Bool                             using (true; false; _∧_) renaming (Bool to T)
open import Data.Fin                              using (Fin; suc; zero; #_; toℕ)
open import Data.List                             using (List; map; all; any; _++_) renaming ([] to ∅; _∷_ to _,_)
open import Data.Nat                              using (ℕ; suc; zero)
open import Data.Product                          using (_,_)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Example.Lexicon where

E = Fin 3

open import Example.Base                                                  E    public
open import Logic.Translation
open import Logic.Classical.Ordered.LambdaCMinus.Type                     Univ public
open import Logic.Classical.Ordered.LambdaCMinus.Structure                Univ public
open import Logic.Classical.Ordered.LambdaCMinus.Judgement                Univ public
open import Logic.Classical.Ordered.LambdaCMinus.Base                     Univ public
open import Logic.Classical.Ordered.LambdaCMinus.ToLinear                 Univ
open import Logic.Classical.Linear.LambdaCMinus.ToUnrestricted            Univ
open import Logic.Classical.Unrestricted.LambdaCMinus.ToAgda              Univ ⟦_⟧ᵁ T
open import Logic.Classical.Unrestricted.LambdaCMinus.EquivalentToIndexed Univ
open import Logic.Classical.Unrestricted.LambdaCMinus.Indexed.Show        Univ public
open import Logic.Intuitionistic.Unrestricted.Agda.Environment                 public


open Translation (Un→Agda ◇ Lin→Un ◇ Ord→Lin) public
open Translation (Un→Ix ◇ Lin→Un ◇ Ord→Lin) public using () renaming ([_] to [_]ˣ)



JOHN   = el NP
MARY   = el NP
BILL   = el NP
LOVES  = (el NP ⇒ el S) ⇐ el NP
PERSON = el N

abstract
  domainₑ : List E
  domainₑ = go
    where
    go : ∀ {n} → List (Fin n)
    go {zero } = ∅
    go {suc n} = zero , map suc go

  forallₑ : (E → T) → T
  forallₑ p = all p domainₑ

  existsₑ : (E → T) → T
  existsₑ p = any p domainₑ

  john mary bill : E
  john = # 0
  mary = # 1
  bill = # 2

  _lovedBy_ : E → E → T
  zero     lovedBy suc zero       = true
  suc zero lovedBy zero           = true
  suc zero lovedBy suc zero       = true
  suc zero lovedBy suc (suc zero) = true
  _        lovedBy _              = false

  person : E → T
  person _ = true

loves : (((T → T) → E → T) → T) → E → T
loves = λ k x → k (λ k y → k (x lovedBy y))
