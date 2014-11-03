------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Algebra using (Monoid)


module Logic.Context where


record Context : Set ℓ where
  field
    monoid : Monoid _ _
