------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


module Logic.Linear.NaturalDeduction {ℓ} (Univ : Set ℓ) where


open import Logic.Linear.Type                       Univ public hiding (module DecEq)
open import Logic.Linear.NaturalDeduction.Structure Univ public hiding (module DecEq)
open import Logic.Linear.NaturalDeduction.Judgement Univ public hiding (module DecEq)
open import Logic.Linear.NaturalDeduction.Base      Univ public
