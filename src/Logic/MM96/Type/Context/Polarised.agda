--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/Type/Context/Polarised.agda
--------------------------------------------------------------------------------


open import Algebra                                    using (Monoid)
open import Function                                   using (flip; _∘_)
open import Data.Product                               using (∃; _×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.MM96.Type.Context.Polarised {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.MM96.Type Atom


infixl 50 _[_]
infixr 30 _⊗>_ _<⊗_
infixr 20 _⇨>_ _<⇨_
infixl 20 _⇦>_ _<⇦_
infixr 30 _⊙>_ _<⊙_
infixr 20 _⇒>_ _<⇒_
infixl 20 _⇐>_ _<⇐_
infixr 40 ◇>_ □>_ ⟨l⟩>_ ⟨r⟩>_


data Context (p : Polarity) : Polarity → Set ℓ where

  []    : Context p p

  ◇>_   : Context p +  → Context p +
  □>_   : Context p +  → Context p +
  ⟨l⟩>_ : Context p +  → Context p +
  ⟨r⟩>_ : Context p +  → Context p +

  _⊗>_  : Type         → Context p +  → Context p +
  _⇒>_  : Type         → Context p -  → Context p -
  _⇐>_  : Type         → Context p +  → Context p -
  _<⊗_  : Context p +  → Type         → Context p +
  _<⇒_  : Context p +  → Type         → Context p -
  _<⇐_  : Context p -  → Type         → Context p -

  _⊙>_  : Type         → Context p +  → Context p +
  _⇦>_  : Type         → Context p +  → Context p -
  _⇨>_  : Type         → Context p -  → Context p -
  _<⊙_  : Context p +  → Type         → Context p +
  _<⇨_  : Context p +  → Type         → Context p -
  _<⇦_  : Context p -  → Type         → Context p -



_[_] : ∀ {p₁ p₂} → Context p₁ p₂ → Type → Type
[]        [ A ] = A
(⟨l⟩>   B)  [ A ] = ⟨l⟩ (B [ A ])
(⟨r⟩>   B)  [ A ] = ⟨r⟩ (B [ A ])
(◇>   B)  [ A ] = ◇ (B [ A ])
(□>   B)  [ A ] = □ (B [ A ])
(B ⊗> C)  [ A ] = B ⊗ (C [ A ])
(C <⊗ B)  [ A ] = (C [ A ]) ⊗ B
(B ⇒> C)  [ A ] = B ⇒ (C [ A ])
(C <⇒ B)  [ A ] = (C [ A ]) ⇒ B
(B ⇐> C)  [ A ] = B ⇐ (C [ A ])
(C <⇐ B)  [ A ] = (C [ A ]) ⇐ B
(B ⊙> C)  [ A ] = B ⊙ (C [ A ])
(C <⊙ B)  [ A ] = (C [ A ]) ⊙ B
(B ⇦> C)  [ A ] = B ⇦ (C [ A ])
(C <⇦ B)  [ A ] = (C [ A ]) ⇦ B
(B ⇨> C)  [ A ] = B ⇨ (C [ A ])
(C <⇨ B)  [ A ] = (C [ A ]) ⇨ B
