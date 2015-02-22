------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function                                   using (_∘_)
open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

module Logic.Classical.Ordered.LambekGrishin.Structure.Polarised {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type      Univ
open import Logic.Classical.Ordered.LambekGrishin.Structure Univ
            as Unpolarised hiding (module Structure; Structure)


infix  10 ·_·
infixr 20 _⇒_
infixl 20 _⇐_
infixl 25 _⇚_
infixr 25 _⇛_
infixr 30 _⊗_
infixr 30 _⊕_


data Structure : Polarity → Set ℓ where
  ·_· : {p  : Polarity}    (A  : Type)        → Structure p
  _⊗_ : (Γ⁺ : Structure +) (Δ⁺ : Structure +) → Structure +
  _⇚_ : (Γ⁺ : Structure +) (Δ⁻ : Structure -) → Structure +
  _⇛_ : (Γ⁻ : Structure -) (Δ⁺ : Structure +) → Structure +
  _⊕_ : (Γ⁻ : Structure -) (Δ⁻ : Structure -) → Structure -
  _⇒_ : (Γ⁺ : Structure +) (Δ⁻ : Structure -) → Structure -
  _⇐_ : (Γ⁻ : Structure -) (Δ⁺ : Structure +) → Structure -


data Polarised : Polarity → Unpolarised.Structure → Set ℓ where
  ·_· : ∀ {p}   (A  : Type)                               → Polarised p (· A ·)
  _⊗_ : ∀ {Γ Δ} (Γ⁺ : Polarised + Γ) (Δ⁺ : Polarised + Δ) → Polarised + (Γ ⊗ Δ)
  _⇚_ : ∀ {Γ Δ} (Γ⁺ : Polarised + Γ) (Δ⁻ : Polarised - Δ) → Polarised + (Γ ⇚ Δ)
  _⇛_ : ∀ {Γ Δ} (Γ⁻ : Polarised - Γ) (Δ⁺ : Polarised + Δ) → Polarised + (Γ ⇛ Δ)
  _⊕_ : ∀ {Γ Δ} (Γ⁻ : Polarised - Γ) (Δ⁻ : Polarised - Δ) → Polarised - (Γ ⊕ Δ)
  _⇒_ : ∀ {Γ Δ} (Γ⁺ : Polarised + Γ) (Δ⁻ : Polarised - Δ) → Polarised - (Γ ⇒ Δ)
  _⇐_ : ∀ {Γ Δ} (Γ⁻ : Polarised - Γ) (Δ⁺ : Polarised + Δ) → Polarised - (Γ ⇐ Δ)


module Correct where
  -- We can attempt to prove correctness in the following manner:
  --
  --  1. define a function `forget` which syntactically transforms a
  --     polarised context to a context (done with a macro to ensure
  --     that there are no typos.
  --
  --  2. proved a proof that `forget` returns the correct context, i.e.
  --     the context for which we've given a polarity proof.
  --
  -- What this gives us is the certainty that we didn't make any typos
  -- in the definition of `Polarised`, esp. in the matching of `Polarised`
  -- constructors to `Context` constructors... *snore*

  forget : ∀ {p Γ} (Γᴾ : Polarised p Γ) → Unpolarised.Structure
  forget (· A ·) = · A ·
  forget (Γ ⊗ Δ) = forget Γ ⊗ forget Δ
  forget (Γ ⇚ Δ) = forget Γ ⇚ forget Δ
  forget (Γ ⇛ Δ) = forget Γ ⇛ forget Δ
  forget (Γ ⊕ Δ) = forget Γ ⊕ forget Δ
  forget (Γ ⇒ Δ) = forget Γ ⇒ forget Δ
  forget (Γ ⇐ Δ) = forget Γ ⇐ forget Δ

  forget-correct : ∀ {p A} (Aᴾ : Polarised p A) → forget Aᴾ ≡ A
  forget-correct (· A ·) = refl
  forget-correct (Γ ⊗ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
  forget-correct (Γ ⇚ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
  forget-correct (Γ ⇛ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
  forget-correct (Γ ⊕ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
  forget-correct (Γ ⇒ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
  forget-correct (Γ ⇐ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
