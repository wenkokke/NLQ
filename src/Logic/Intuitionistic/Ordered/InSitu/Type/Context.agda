------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Intuitionistic.Ordered.InSitu.Type.Context {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Ordered.InSitu.Type Univ


infixr 20 _⊗>_ _∘>_
infixr 30 _⇒>_ _⇨>_ _⇐>_ _⇦>_
infixl 20 _<⊗_ _<∘_
infixl 30 _<⇒_ _<⇨_ _<⇐_ _<⇦_


data Context : Set ℓ where

  []  : Context

  ◇>_  : Context → Context
  □>_  : Context → Context

  _⊗>_ : Type → Context → Context
  _⇒>_ : Type → Context → Context
  _⇐>_ : Type → Context → Context
  _∘>_ : Type → Context → Context
  _⇨>_ : Type → Context → Context
  _⇦>_ : Type → Context → Context

  _<⊗_ : Context → Type → Context
  _<⇒_ : Context → Type → Context
  _<⇐_ : Context → Type → Context
  _<∘_ : Context → Type → Context
  _<⇨_ : Context → Type → Context
  _<⇦_ : Context → Type → Context


_[_] : Context → Type → Type
[]       [ A ] = A
(◇>   Σ) [ A ] = ◇ (Σ [ A ])
(□>   Σ) [ A ] = □ (Σ [ A ])
(B ⊗> Σ) [ A ] = B ⊗ (Σ [ A ])
(B ⇒> Σ) [ A ] = B ⇒ (Σ [ A ])
(B ⇐> Σ) [ A ] = B ⇐ (Σ [ A ])
(B ∘> Σ) [ A ] = B ∘ (Σ [ A ])
(B ⇨> Σ) [ A ] = B ⇨ (Σ [ A ])
(B ⇦> Σ) [ A ] = B ⇦ (Σ [ A ])
(Σ <⊗ B) [ A ] = (Σ [ A ]) ⊗ B
(Σ <⇒ B) [ A ] = (Σ [ A ]) ⇒ B
(Σ <⇐ B) [ A ] = (Σ [ A ]) ⇐ B
(Σ <∘ B) [ A ] = (Σ [ A ]) ∘ B
(Σ <⇨ B) [ A ] = (Σ [ A ]) ⇨ B
(Σ <⇦ B) [ A ] = (Σ [ A ]) ⇦ B
