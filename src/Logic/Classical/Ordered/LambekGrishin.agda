------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Classical.Ordered.LambekGrishin {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type              Univ public hiding (module DecEq)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement  Univ public hiding (module DecEq)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base       Univ public
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Derivation Univ public
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Trans      Univ public
