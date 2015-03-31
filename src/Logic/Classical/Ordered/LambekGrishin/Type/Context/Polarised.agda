------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Algebra                                    using (Monoid)
open import Function                                   using (flip; _∘_)
open import Data.Product                               using (∃; _×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Ordered.LambekGrishin.Type.Context.Polarised {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type Univ


infixr 30 _⊗>_ _<⊗_
infixr 20 _⇛>_ _<⇛_
infixl 20 _⇚>_ _<⇚_
infixr 30 _⊕>_ _<⊕_
infixr 20 _⇒>_ _<⇒_
infixl 20 _⇐>_ _<⇐_


data Context (p : Polarity) : Polarity → Set ℓ where
  []    : Context p p
  □>_   : Context p -  → Context p -
  ◇>_   : Context p +  → Context p +
  ₀>_   : Context p +  → Context p -
  _<⁰   : Context p +  → Context p -
  ₁>_   : Context p -  → Context p +
  _<¹   : Context p -  → Context p +
  _⊗>_  : Type         → Context p +  → Context p +
  _⇒>_  : Type         → Context p -  → Context p -
  _⇐>_  : Type         → Context p +  → Context p -
  _<⊗_  : Context p +  → Type         → Context p +
  _<⇒_  : Context p +  → Type         → Context p -
  _<⇐_  : Context p -  → Type         → Context p -
  _⊕>_  : Type         → Context p -  → Context p -
  _⇚>_  : Type         → Context p -  → Context p +
  _⇛>_  : Type         → Context p +  → Context p +
  _<⊕_  : Context p -  → Type         → Context p -
  _<⇚_  : Context p +  → Type         → Context p +
  _<⇛_  : Context p -  → Type         → Context p +


_[_] : ∀ {p₁ p₂} → Context p₁ p₂ → Type → Type
[]        [ A ] = A
(□> B)    [ A ] = □ (B [ A ])
(◇> B)    [ A ] = ◇ (B [ A ])
(₀> B)    [ A ] = ₀ (B [ A ])
(₁> B)    [ A ] = ₁ (B [ A ])
(B <⁰)    [ A ] = (B [ A ]) ⁰
(B <¹)    [ A ] = (B [ A ]) ¹
(B ⊗> C)  [ A ] = B ⊗ (C [ A ])
(C <⊗ B)  [ A ] = (C [ A ]) ⊗ B
(B ⇒> C)  [ A ] = B ⇒ (C [ A ])
(C <⇒ B)  [ A ] = (C [ A ]) ⇒ B
(B ⇐> C)  [ A ] = B ⇐ (C [ A ])
(C <⇐ B)  [ A ] = (C [ A ]) ⇐ B
(B ⊕> C)  [ A ] = B ⊕ (C [ A ])
(C <⊕ B)  [ A ] = (C [ A ]) ⊕ B
(B ⇚> C)  [ A ] = B ⇚ (C [ A ])
(C <⇚ B)  [ A ] = (C [ A ]) ⇚ B
(B ⇛> C)  [ A ] = B ⇛ (C [ A ])
(C <⇛ B)  [ A ] = (C [ A ]) ⇛ B
