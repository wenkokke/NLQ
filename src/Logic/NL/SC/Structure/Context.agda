------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.NL.SC.Structure.Context {ℓ} (Atom : Set ℓ) where


open import Logic.NL.SC.Structure Atom


infixr 5 _,>_
infixl 5 _<,_
infixl 4 _[_]


data Context : Set ℓ where
  []    : Context
  _<,_  : (Γ : Context)   (Δ : Structure) → Context
  _,>_  : (Γ : Structure) (Δ : Context)   → Context


_[_] : Context → Structure → Structure
[]       [ Δ ] = Δ
Γ ,> Γ′  [ Δ ] = Γ , (Γ′ [ Δ ])
Γ <, Γ′  [ Δ ] = (Γ [ Δ ]) , Γ′
