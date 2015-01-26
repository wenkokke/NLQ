module Logic.Classical.Judgement {ℓ} (Anta : Set ℓ) (Type : Set ℓ) (Succ : Set ℓ) where


infix 3 _⊢_ _⊢[_]_


data Judgement : Set ℓ where
  _⊢_    : Anta →        Succ → Judgement
  _⊢[_]_ : Anta → Type → Succ → Judgement
