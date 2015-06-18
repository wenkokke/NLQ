------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Classical.Ordered.LambekGrishin.ResMon {ℓ} (Atom : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type             Atom public hiding (module DecEq)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement Atom public hiding (module DecEq)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base      Atom public
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Trans     Atom public
