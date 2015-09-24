--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon.agda
--------------------------------------------------------------------------------


module Logic.NLP.ResMon {ℓ} (Atom : Set ℓ) where


open import Logic.NLP.Type             Atom public hiding (module DecEq)
open import Logic.NLP.ResMon.Sequent Atom public hiding (module DecEq)
open import Logic.NLP.ResMon.Base      Atom public
open import Logic.NLP.ResMon.Cut       Atom public
