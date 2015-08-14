------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.NLIBC.Type.Context.Polarised {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.NLIBC.Type Atom


infix  50 _[_]
infixr 20 _⊗>_ _∘>_
infixr 30 _⇒>_ _⇨>_ _⇐>_ _⇦>_
infixl 20 _<⊗_ _<∘_
infixl 30 _<⇒_ _<⇨_ _<⇐_ _<⇦_


data Context : Polarity → Set ℓ where

  []   : ∀ {p} → Context p

  _⊗>_ : Type → Context + → Context +
  _⇒>_ : Type → Context - → Context -
  _⇐>_ : Type → Context + → Context -
  _∘>_ : Type → Context + → Context +
  _⇨>_ : Type → Context - → Context -
  _⇦>_ : Type → Context + → Context -

  _<⊗_ : Context + → Type → Context +
  _<⇒_ : Context + → Type → Context -
  _<⇐_ : Context - → Type → Context -
  _<∘_ : Context + → Type → Context +
  _<⇨_ : Context + → Type → Context -
  _<⇦_ : Context - → Type → Context -


_[_] : ∀ {p} → Context p → Type → Type
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
