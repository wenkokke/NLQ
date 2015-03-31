------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra                                         using (module Monoid)
open import Function                                        using (_∘_)
open import Data.List                                       using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum                                        using (_⊎_; inj₁; inj₂)
open import Data.Product                                    using (∃; _×_; _,_)
open import Relation.Nullary                                using (Dec; yes; no)
open import Relation.Nullary.Decidable                      using (True; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)


module Logic.Classical.Ordered.LambekGrishin.ResMon.ToIntuitionisticLinearLambda {ℓ} (Univ : Set ℓ) (⊥ : Univ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.Classical.Ordered.LambekGrishin.Type             Univ as LGT
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement Univ as LGJ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base      Univ as LG

open import Logic.Intuitionistic.Linear.Lambda.Type      Univ as ΛT
open import Logic.Intuitionistic.Linear.Lambda.Judgement Univ as ΛJ
open import Logic.Intuitionistic.Linear.Lambda.Base      Univ as Λ
open import Logic.Intuitionistic.Linear.Lambda.Permute   Univ as ΛP
open Monoid (Data.List.monoid ΛT.Type) using (assoc)
