------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


module Logic.Lambek.NaturalDeduction {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type                                Univ public hiding (module DecEq)
open import Logic.Lambek.ResMon.Judgement                    Univ public hiding (module DecEq)
open import Logic.Lambek.NaturalDeduction.Base               Univ public
open import Logic.Lambek.NaturalDeduction.EquivalentToResMon Univ public
open import Logic.Lambek.NaturalDeduction.Complete           Univ public
