------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level            using (zero)
open import Data.Product     using (Σ; _,_; proj₁; proj₂)
open import Data.Traversable using (module RawTraversable)


module Example.System.NLIBC where


open import Example.System.Base                   public
open import Logic.Grammar                         public
open import Logic.NLIBC             Atom          public
open import Logic.NLIBC.ProofSearch Atom _≟-Atom_ public
open import Logic.NLIBC.ToAgda      Atom ⟦_⟧ᴬ     public


open RawTraversable (rawTraversable {zero}) using (_<$>_)


s n np inf pp a iv tv : Type
s   = el S
n   = el N
np  = el NP
inf = el INF
pp  = el PP
a   = n ⇐ n
iv  = np ⇒ s
tv  = iv ⇐ np


private
  flatten : Struct Type → Structure
  flatten ·  A  · = · A ·
  flatten ⟨  X  ⟩ = flatten X
  flatten (X , Y) = flatten X ∙ flatten Y

  combine : (Γ : Struct (Σ Type ⟦_⟧ᵗ)) → ⟦ flatten (proj₁ <$> Γ) ⟧ˢ
  combine ·  p  · = proj₂ p
  combine ⟨  Γ  ⟩ = combine Γ
  combine (Γ , Δ) = combine Γ , combine Δ


instance
  grammar : Grammar
  grammar = record
    { Type           = Type
    ; Struct         = Struct
    ; rawTraversable = rawTraversable
    ; _⊢_            = λ Γ p → NL (flatten Γ ⊢ p)
    ; findAll        = λ Γ p → findAll (flatten Γ ⊢ p)
    ; s              = el S
    ; ⟦_⟧ᵗ           = ⟦_⟧ᵗ
    ; ⟦_⟧            = λ Γ f → ⟦ f ⟧ (combine Γ)
    }
