------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


module Logic.Lambek.ResMon {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.ResMon.Judgement Univ public
open import Logic.Lambek.ResMon.Base      Univ public
open import Logic.Lambek.ResMon.Trans     Univ public
open import Logic.Lambek.ResMon.Complete  Univ public
