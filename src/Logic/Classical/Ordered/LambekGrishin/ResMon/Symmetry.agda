------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Ordered.LambekGrishin.ResMon.Symmetry {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type                               Univ
open import Logic.Classical.Ordered.LambekGrishin.Type.Context.Polarised             Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement                   Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement.Context.Polarised Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base                        Univ
