--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (module DecSetoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.NLP.DispCalc.Sequent {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.NLP.DispCalc.Type      Atom
open import Logic.NLP.DispCalc.Structure Atom


infix 3 _⊢_ _⊢[_] [_]⊢_
infixl 50 _⋈ʲ


data Sequent : Set ℓ where
  _⊢_    : (Γ⁺ : Structure +) (Δ⁻ : Structure -) → Sequent
  [_]⊢_  : (A  : Type)        (Δ⁻ : Structure -) → Sequent
  _⊢[_]  : (Γ⁺ : Structure +) (Δ⁻ : Type       ) → Sequent


_⋈ʲ : Sequent → Sequent
(  Γ⁺  ⊢  Δ⁻  ) ⋈ʲ = ( Γ⁺ ⋈ˢ )⊢( Δ⁻ ⋈ˢ )
([ A  ]⊢  Δ⁻  ) ⋈ʲ = [ A  ⋈ᵗ ]⊢( Δ⁻ ⋈ˢ )
(  Γ⁺  ⊢[ B  ]) ⋈ʲ = ( Γ⁺ ⋈ˢ )⊢[ B ⋈ᵗ ]
