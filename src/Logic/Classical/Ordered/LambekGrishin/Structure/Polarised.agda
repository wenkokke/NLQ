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
infix  15 [_] ⟨_⟩
infixr 20 _⇒_ _⇐_
infixl 25 _⇚_ _⇛_
infixr 30 _⊗_ _⊕_


data Structure : Polarity → Set ℓ where
  ·_· : {p  : Polarity}    (A  : Type)        → Structure p
  [_] : (Γ⁻ : Structure -)                    → Structure -
  ⟨_⟩ : (Γ⁺ : Structure +)                    → Structure +
  ₀_  : (Γ⁻ : Structure +)                    → Structure -
  _⁰  : (Γ⁻ : Structure +)                    → Structure -
  ₁_  : (Γ⁺ : Structure -)                    → Structure +
  _¹  : (Γ⁺ : Structure -)                    → Structure +
  _⊗_ : (Γ⁺ : Structure +) (Δ⁺ : Structure +) → Structure +
  _⇚_ : (Γ⁺ : Structure +) (Δ⁻ : Structure -) → Structure +
  _⇛_ : (Γ⁻ : Structure -) (Δ⁺ : Structure +) → Structure +
  _⊕_ : (Γ⁻ : Structure -) (Δ⁻ : Structure -) → Structure -
  _⇒_ : (Γ⁺ : Structure +) (Δ⁻ : Structure -) → Structure -
  _⇐_ : (Γ⁻ : Structure -) (Δ⁺ : Structure +) → Structure -


data Polarised : Polarity → Unpolarised.Structure → Set ℓ where
  ·_· : ∀ {p}   (A  : Type)                               → Polarised p (· A ·)
  [_] : ∀ {Γ}   (Γ⁻ : Polarised - Γ)                      → Polarised - ([ Γ ])
  ⟨_⟩ : ∀ {Γ}   (Γ⁺ : Polarised + Γ)                      → Polarised + (⟨ Γ ⟩)
  ₀_  : ∀ {Γ}   (Γ⁻ : Polarised + Γ)                      → Polarised - (₀   Γ)
  _⁰  : ∀ {Γ}   (Γ⁻ : Polarised + Γ)                      → Polarised - (Γ   ⁰)
  ₁_  : ∀ {Γ}   (Γ⁺ : Polarised - Γ)                      → Polarised + (₁   Γ)
  _¹  : ∀ {Γ}   (Γ⁺ : Polarised - Γ)                      → Polarised + (Γ   ¹)
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
  forget ([ Γ ]) = [ forget Γ ]
  forget (⟨ Γ ⟩) = ⟨ forget Γ ⟩
  forget (₀   Γ) = ₀ forget Γ
  forget (Γ   ⁰) = forget Γ ⁰
  forget (₁   Γ) = ₁ forget Γ
  forget (Γ   ¹) = forget Γ ¹
  forget (Γ ⊗ Δ) = forget Γ ⊗ forget Δ
  forget (Γ ⇚ Δ) = forget Γ ⇚ forget Δ
  forget (Γ ⇛ Δ) = forget Γ ⇛ forget Δ
  forget (Γ ⊕ Δ) = forget Γ ⊕ forget Δ
  forget (Γ ⇒ Δ) = forget Γ ⇒ forget Δ
  forget (Γ ⇐ Δ) = forget Γ ⇐ forget Δ

  forget-correct : ∀ {p A} (Aᴾ : Polarised p A) → forget Aᴾ ≡ A
  forget-correct (· A ·) = refl
  forget-correct ([ Γ ]) rewrite forget-correct Γ = refl
  forget-correct (⟨ Γ ⟩) rewrite forget-correct Γ = refl
  forget-correct (₀   Γ) rewrite forget-correct Γ = refl
  forget-correct (Γ   ⁰) rewrite forget-correct Γ = refl
  forget-correct (₁   Γ) rewrite forget-correct Γ = refl
  forget-correct (Γ   ¹) rewrite forget-correct Γ = refl
  forget-correct (Γ ⊗ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
  forget-correct (Γ ⇚ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
  forget-correct (Γ ⇛ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
  forget-correct (Γ ⊕ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
  forget-correct (Γ ⇒ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
  forget-correct (Γ ⇐ Δ) rewrite forget-correct Γ | forget-correct Δ = refl
