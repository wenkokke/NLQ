------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level                                 using ()
open import Category.Functor                      using (module RawFunctor; RawFunctor)
open import Data.Nat                              using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties.Simple as ℕ       using ()
open import Data.Fin                              using (Fin; suc; zero)
open import Data.Maybe                            using (Maybe; just; nothing)
open import Data.Product                          using (_×_; _,_; proj₁; proj₂)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans; cong; refl)


module Logic.NLP.SC.Structure.Context {ℓ} (Atom : Set ℓ) where


open import Logic.NLP.SC.Structure Atom


infixr 30 _∙>_
infixl 30 _<∙_
infix 50 _[_] _<_>

data Context : Set ℓ where
  []    : Context
  _∙>_  : Structure → Context   → Context
  _<∙_  : Context   → Structure → Context

_<_> : Context → Context → Context
[]       < Δ > = Δ
(q ∙> Γ) < Δ > = q ∙> (Γ < Δ >)
(Γ <∙ q) < Δ > = (Γ < Δ >) <∙ q

_[_] : Context → Structure → Structure
[]        [ Δ ] = Δ
(Γ ∙> Γ′) [ Δ ] = Γ ∙ (Γ′ [ Δ ])
(Γ <∙ Γ′) [ Δ ] = (Γ [ Δ ]) ∙ Γ′

<>-def : ∀ Γ Δ p → (Γ [ Δ [ p ] ]) ≡ ((Γ < Δ >) [ p ])
<>-def    []    Δ p = refl
<>-def (_ ∙> Γ) Δ p rewrite <>-def Γ Δ p = refl
<>-def (Γ <∙ _) Δ p rewrite <>-def Γ Δ p = refl
