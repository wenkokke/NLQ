------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


module Logic.NL.PG99 {ℓ} (Atom : Set ℓ) where


open import Logic.NL.PG99.Judgement Atom public
open import Logic.NL.PG99.Base      Atom public
open import Logic.NL.PG99.Cut       Atom public
