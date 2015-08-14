------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.LG.ResMon {ℓ} (Atom : Set ℓ) where


open import Logic.LG.Type             Atom public hiding (module DecEq)
open import Logic.LG.ResMon.Judgement Atom public hiding (module DecEq)
open import Logic.LG.ResMon.Base      Atom public
open import Logic.LG.ResMon.Cut       Atom public
