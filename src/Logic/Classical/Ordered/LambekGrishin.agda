------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Classical.Ordered.LambekGrishin {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type       Univ public
open import Logic.Classical.Ordered.LambekGrishin.Judgement  Univ public
open import Logic.Classical.Ordered.LambekGrishin.Base       Univ public
open import Logic.Classical.Ordered.LambekGrishin.Derivation Univ public
open import Logic.Classical.Ordered.LambekGrishin.Trans      Univ public
