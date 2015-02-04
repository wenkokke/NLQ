------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Data.Empty using (⊥)


module Logic.Classical.Ordered.LambekGrishin {ℓ} (Univ : Set ℓ) where


open import Logic.Type                                       Univ public
open import Logic.Judgement                           Type ⊥ Type public
open import Logic.Classical.Ordered.LambekGrishin.Base       Univ public
open import Logic.Classical.Ordered.LambekGrishin.Derivation Univ public
open import Logic.Classical.Ordered.LambekGrishin.Trans      Univ public
