--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Judgement/Context/Polarised.agda
--------------------------------------------------------------------------------


open import Level                                      using (zero)
open import Algebra                                    using (Monoid)
open import Function                                   using (id; flip; _∘_)
open import Data.Empty                                 using (⊥)
open import Data.Product                               using (∃; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Unit                                  using (⊤; tt)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.MM96.ResMon.Judgement.Context.Polarised {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.MM96.Type                     Atom as T
open import Logic.MM96.Type.Context.Polarised   Atom as TCP
open import Logic.MM96.ResMon.Judgement         Atom


infix 50 _[_]ᴶ
infix 3 _<⊢_ _⊢>_


data Contextᴶ (p : Polarity) : Set ℓ where
  _<⊢_  : Context p +  → Type         → Contextᴶ p
  _⊢>_  : Type         → Context p -  → Contextᴶ p



_[_]ᴶ : ∀ {p} → Contextᴶ p → Type → Judgement
(A <⊢ B) [ C ]ᴶ = A [ C ] ⊢ B
(A ⊢> B) [ C ]ᴶ = A ⊢ B [ C ]


