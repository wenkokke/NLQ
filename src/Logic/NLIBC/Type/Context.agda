------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.NLIBC.Type.Context {ℓ} (Atom : Set ℓ) where


open import Logic.NLIBC.Type Atom


infixr 20 _⊗>_ _∘>_
infixr 30 _⇒>_ _⇨>_ _⇐>_ _⇦>_
infixl 20 _<⊗_ _<∘_
infixl 30 _<⇒_ _<⇨_ _<⇐_ _<⇦_


data Context : Set ℓ where

  []  : Context

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
[]       [ x ] = x
(y ⊗> Σ) [ x ] = y ⊗ (Σ [ x ])
(y ⇒> Σ) [ x ] = y ⇒ (Σ [ x ])
(y ⇐> Σ) [ x ] = y ⇐ (Σ [ x ])
(y ∘> Σ) [ x ] = y ∘ (Σ [ x ])
(y ⇨> Σ) [ x ] = y ⇨ (Σ [ x ])
(y ⇦> Σ) [ x ] = y ⇦ (Σ [ x ])
(Σ <⊗ y) [ x ] = (Σ [ x ]) ⊗ y
(Σ <⇒ y) [ x ] = (Σ [ x ]) ⇒ y
(Σ <⇐ y) [ x ] = (Σ [ x ]) ⇐ y
(Σ <∘ y) [ x ] = (Σ [ x ]) ∘ y
(Σ <⇨ y) [ x ] = (Σ [ x ]) ⇨ y
(Σ <⇦ y) [ x ] = (Σ [ x ]) ⇦ y
