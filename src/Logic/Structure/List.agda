open import Data.List using (List; _++_) renaming ([] to ∅; _∷_ to _,_)


module Logic.Structure.List {ℓ} (Univ : Set ℓ) where


open import Logic.Type Univ


infix 4 _[_]

data Hole : Set where
  □ : Hole

data Context : Set ℓ where
  _<,_ : Hole → List Type → Context
  _,>_ : Type → Context   → Context

_[_] : Context → List Type → List Type
(□ <, Γ₁) [ Γ₂ ] = Γ₂ ++ Γ₁
(A ,> Γ₁) [ Γ₂ ] = A , (Γ₁ [ Γ₂ ])
