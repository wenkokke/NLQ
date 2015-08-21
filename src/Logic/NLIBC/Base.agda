------------------------------------------------------------------------
-- The Lambek Calculus in pgda
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality using (sym)


module Logic.NLIBC.Base {ℓ} (Atom : Set ℓ) where


open import Logic.NLIBC.Type              Atom
open import Logic.NLIBC.Structure         Atom
open import Logic.NLIBC.Structure.Context Atom
open import Logic.NLIBC.Judgement         Atom


infix 1 NL_ _⊢NL_


mutual
  _⊢NL_ : Structure → Type → Set ℓ
  Γ ⊢NL p = NL Γ ⊢ p


  data NL_ : Judgement → Set ℓ where

    ax   : ∀ {p}
         → · p · ⊢NL p

    -- rules for (⇐, ∙, ⇒)

    ⇒ᴸ   : ∀ {Γ Δ p q r}
         → Γ                   ⊢NL p
         → Δ [ · q · ]         ⊢NL r
         → Δ [ Γ ∙ · p ⇒ q · ] ⊢NL r

    ⇒ᴿ   : ∀ {Γ p q}
         → · p · ∙ Γ           ⊢NL q
         →         Γ           ⊢NL p ⇒ q

    ⇐ᴸ   : ∀ {Γ Δ p q r}
         → Γ                   ⊢NL p
         → Δ [ · q · ]         ⊢NL r
         → Δ [ · q ⇐ p · ∙ Γ ] ⊢NL r

    ⇐ᴿ   : ∀ {Γ p q}
         → Γ ∙ · p ·           ⊢NL q
         → Γ                   ⊢NL q ⇐ p


    -- rules for (⇦, ∘, ⇨)

    ⇨ᴸ   : ∀ {Γ Δ p q r}
         → Γ                   ⊢NL p
         → Δ [ · q · ]         ⊢NL r
         → Δ [ Γ ∘ · p ⇨ q · ] ⊢NL r

    ⇨ᴿ   : ∀ {Γ p q}
         → · p · ∘ Γ           ⊢NL q
         →         Γ           ⊢NL p ⇨ q

    ⇦ᴸ   : ∀ {Γ Δ p q r}
         → Γ                   ⊢NL p
         → Δ [ · q · ]         ⊢NL r
         → Δ [ · q ⇦ p · ∘ Γ ] ⊢NL r

    ⇦ᴿ   : ∀ {Γ p q}
         → Γ ∘ · p ·           ⊢NL q
         → Γ                   ⊢NL q ⇦ p


    -- structural postulates for (I, B, C)

    Iᵢ   : ∀ {Γ p q}
         → Γ [ p ∘ I ] ⊢NL q
         → Γ [ p     ] ⊢NL q

    Iₑ   : ∀ {Γ p q}
         → Γ [ p     ] ⊢NL q
         → Γ [ p ∘ I ] ⊢NL q

    Bᵢ   : ∀ {Γ p q r s}
         → Γ [ q ∘ ((B ∙ p) ∙ r) ] ⊢NL s
         → Γ [ p ∙ (q ∘ r) ]       ⊢NL s

    Bₑ   : ∀ {Γ p q r s}
         → Γ [ p ∙ (q ∘ r) ]       ⊢NL s
         → Γ [ q ∘ ((B ∙ p) ∙ r) ] ⊢NL s

    Cᵢ   : ∀ {Γ p q r s}
         → Γ [ p ∘ ((C ∙ q) ∙ r) ] ⊢NL s
         → Γ [ (p ∘ q) ∙ r ]       ⊢NL s

    Cₑ   : ∀ {Γ p q r s}
         → Γ [ (p ∘ q) ∙ r ]       ⊢NL s
         → Γ [ p ∘ ((C ∙ q) ∙ r) ] ⊢NL s


Trace : (Γ : Contextᵀ) → Structure
Trace    []    = I
Trace (p ∙> Γ) = (B ∙ p) ∙ Trace Γ
Trace (Γ <∙ r) = (C ∙ Trace Γ) ∙ r


-- In the base case (Γ is []):
--
--        Insert the identity element under Σ.
--
-- Otherwise (Γ is (∙ q)/(q ∙)):
--
-- (lem₁) Convince Agda that we can add the (∙ q)/(q ∙) to the Σ.
--        Recursively call `up`.
-- (lem₂) Convince Agda that we can remove the (∙ q)/(q ∙) from the Σ.
--        Push Δ upwards, past the (∙ q)/(q ∙).
--
up   : ∀ (Σ : Context) (Γ : Contextᵀ) {Δ p}
     → Σ [ Δ ∘ Trace Γ ] ⊢NL p → Σ [ Γ [ Δ ]ᵀ ] ⊢NL p
up   Σ [] f = Iᵢ {Γ = Σ} f
up   Σ (q ∙> Γ) {Δ} f = lem₁
  where
    lem₂ : (Σ < q ∙> [] >) [ Δ ∘ Trace Γ ] ⊢NL _
    lem₂ rewrite sym (<>-def Σ (q ∙> []) (Δ ∘ Trace Γ)) = Bᵢ {Σ} f
    lem₁ : Σ [ q ∙> Γ [ Δ ]ᵀ ] ⊢NL _
    lem₁ rewrite <>-def Σ (q ∙> []) (Γ [ Δ ]ᵀ) = up (Σ < q ∙> [] >) Γ lem₂
up   Σ (Γ <∙ q) {Δ} f = lem₁
  where
    lem₂ : (Σ < [] <∙ q >) [ Δ ∘ Trace Γ ] ⊢NL _
    lem₂ rewrite sym (<>-def Σ ([] <∙ q) (Δ ∘ Trace Γ)) = Cᵢ {Σ} f
    lem₁ : Σ [ (Γ [ Δ ]ᵀ) ∙ q ] ⊢NL _
    lem₁ rewrite <>-def Σ ([] <∙ q) (Γ [ Δ ]ᵀ) = up (Σ < [] <∙ q >) Γ lem₂



-- In the base case (Γ is []):
--
--        Remove the identity element under Σ.
--
-- Otherwise (Γ is (∙ q)/(q ∙)):
--
--        Push Δ downwards, past the (∙ q)/(q ∙).
-- (lem₁) Convince Agda that we can add the (∙ q)/(q ∙) to the Σ.
--        Call `down` recursively.
-- (lem₂) Convince Agda that we can remove the (∙ q)/(q ∙) from the Σ.
--
down : ∀ (Σ : Context) (Γ : Contextᵀ) {Δ p}
     → Σ [ Γ [ Δ ]ᵀ ] ⊢NL p → Σ [ Δ ∘ Trace Γ ] ⊢NL p
down Σ [] f = Iₑ {Σ} f
down Σ (q ∙> Γ) {Δ} f = Bₑ {Σ} lem₁
  where
    lem₂ : (Σ < q ∙> [] >) [ Γ [ Δ ]ᵀ ] ⊢NL _
    lem₂ rewrite sym (<>-def Σ (q ∙> []) (Γ [ Δ ]ᵀ)) = f
    lem₁ : Σ [ q ∙ Δ ∘ Trace Γ ] ⊢NL _
    lem₁ rewrite <>-def Σ (q ∙> []) (Δ ∘ Trace Γ) = down (Σ < q ∙> [] >) Γ lem₂
down Σ (Γ <∙ q) {Δ} f = Cₑ {Σ} lem₁
  where
    lem₂ : (Σ < [] <∙ q >) [ Γ [ Δ ]ᵀ ] ⊢NL _
    lem₂ rewrite sym (<>-def Σ ([] <∙ q) (Γ [ Δ ]ᵀ)) = f
    lem₁ : Σ [ (Δ ∘ Trace Γ) ∙ q ] ⊢NL _
    lem₁ rewrite <>-def Σ ([] <∙ q) (Δ ∘ Trace Γ) = down (Σ < [] <∙ q >) Γ lem₂
