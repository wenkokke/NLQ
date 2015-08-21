--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon.agda
--------------------------------------------------------------------------------


module Logic.MM96.ResMon {ℓ} (Atom : Set ℓ) where


open import Logic.MM96.Type             Atom public hiding (module DecEq)
open import Logic.MM96.ResMon.Judgement Atom public hiding (module DecEq)
open import Logic.MM96.ResMon.Base      Atom public
