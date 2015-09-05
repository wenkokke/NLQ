------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Fin                                   using (Fin; suc; zero)
open import Data.Nat                                   using (ℕ; suc; zero)
open import Data.Nat.Properties.Simple as ℕ            using ()
open import Data.Product                               using (∃; _,_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl; trans; cong; sym)


module Logic.NLIBC.Base {ℓ} (Atom : Set ℓ) where


open import Logic.NLIBC.Type              Atom
open import Logic.NLIBC.Structure         Atom
open import Logic.NLIBC.Structure.Context Atom
open import Logic.NLIBC.Sequent         Atom


infix 1 NL_ _⊢NL_


mutual
  _⊢NL_ : Structure → Type → Set ℓ
  Γ ⊢NL p = NL Γ ⊢ p


  data NL_ : Sequent → Set ℓ where

    ax   : ∀ {p}
         → · p · ⊢NL p

    -- rules for (⇐, ∙, ⇒)

    ⇒L   : ∀ (Σ : Context) {Γ p q r}
         → Γ                   ⊢NL p
         → Σ [ · q · ]         ⊢NL r
         → Σ [ Γ ∙ · p ⇒ q · ] ⊢NL r

    ⇒R   : ∀ {Γ p q}
         → · p · ∙ Γ           ⊢NL q
         →         Γ           ⊢NL p ⇒ q

    ⇐L   : ∀ (Σ : Context) {Γ p q r}
         → Γ                   ⊢NL p
         → Σ [ · q · ]         ⊢NL r
         → Σ [ · q ⇐ p · ∙ Γ ] ⊢NL r

    ⇐R   : ∀ {Γ p q}
         → Γ ∙ · p ·           ⊢NL q
         → Γ                   ⊢NL q ⇐ p


    -- rules for (⇦, ∘, ⇨)

    ⇨L   : ∀ (Σ : Context) {Γ p q r}
         → Γ                   ⊢NL p
         → Σ [ · q · ]         ⊢NL r
         → Σ [ Γ ∘ · p ⇨ q · ] ⊢NL r

    ⇨R   : ∀ {Γ p q}
         → · p · ∘ Γ           ⊢NL q
         →         Γ           ⊢NL p ⇨ q

    ⇦L   : ∀ (Σ : Context) {Γ p q r}
         → Γ                   ⊢NL p
         → Σ [ · q · ]         ⊢NL r
         → Σ [ · q ⇦ p · ∘ Γ ] ⊢NL r

    ⇦R   : ∀ {Γ p q}
         → Γ ∘ · p ·           ⊢NL q
         → Γ                   ⊢NL q ⇦ p


    -- structural postulates for (I, B, C)

    Iᵢ   : ∀ (Γ : Context) {p q}
         → Γ [ p ∘ I ] ⊢NL q
         → Γ [ p     ] ⊢NL q

    Iₑ   : ∀ (Γ : Context) {p q}
         → Γ [ p     ] ⊢NL q
         → Γ [ p ∘ I ] ⊢NL q

    Bᵢ   : ∀ (Γ : Context) {p q r s}
         → Γ [ q ∘ ((B ∙ p) ∙ r) ] ⊢NL s
         → Γ [ p ∙ (q ∘ r) ]       ⊢NL s

    Bₑ   : ∀ (Γ : Context) {p q r s}
         → Γ [ p ∙ (q ∘ r) ]       ⊢NL s
         → Γ [ q ∘ ((B ∙ p) ∙ r) ] ⊢NL s

    Cᵢ   : ∀ (Γ : Context) {p q r s}
         → Γ [ p ∘ ((C ∙ q) ∙ r) ] ⊢NL s
         → Γ [ (p ∘ q) ∙ r ]       ⊢NL s

    Cₑ   : ∀ (Γ : Context) {p q r s}
         → Γ [ (p ∘ q) ∙ r ]       ⊢NL s
         → Γ [ p ∘ ((C ∙ q) ∙ r) ] ⊢NL s


    -- logical rules for gapping

    ⇨RgL : ∀ (Γ : Context) {p q r}
         → Γ [ · q · ∙ p ] ⊢NL r
         → Γ [ p ] ⊢NL q ⇨ r

    ⇨RgR : ∀ (Γ : Context) {p q r}
         → Γ [ p ∙ · q · ] ⊢NL r
         → Γ [ p ] ⊢NL q ⇨ r


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
up : ∀ (Σ : Context) (Γ : Context₁) {Δ p} → Σ [ Δ ∘ λx Γ [x] ] ⊢NL p → Σ [ Γ [ Δ ] ] ⊢NL p
up Σ []       {Δ} f = Iᵢ Σ f
up Σ (q ∙> Γ) {Δ} f = lem₁
  where
  lem₂ : Σ < q ∙> [] > [ Δ ∘ λx Γ [x] ] ⊢NL _
  lem₂ rewrite sym (<>-def Σ (q ∙> []) (Δ ∘ λx Γ [x])) = Bᵢ Σ f
  lem₁ : Σ [ q ∙ Γ [ Δ ] ] ⊢NL _
  lem₁ rewrite     (<>-def Σ (q ∙> []) (Γ [ Δ ])) = up (Σ < q ∙> [] >) Γ lem₂
up Σ (Γ <∙ q) {Δ} f = lem₁
  where
  lem₂ : Σ < [] <∙ q > [ Δ ∘ λx Γ [x] ] ⊢NL _
  lem₂ rewrite sym (<>-def Σ ([] <∙ q) (Δ ∘ λx Γ [x])) = Cᵢ Σ f
  lem₁ : Σ [ Γ [ Δ ] ∙ q ] ⊢NL _
  lem₁ rewrite     (<>-def Σ ([] <∙ q) (Γ [ Δ ])) = up (Σ < [] <∙ q >) Γ lem₂



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
down : ∀ (Σ : Context) (Γ : Context₁) {Δ p} → Σ [ Γ [ Δ ] ] ⊢NL p → Σ [ Δ ∘ λx Γ [x] ] ⊢NL p
down Σ []       {Δ} f = Iₑ Σ f
down Σ (q ∙> Γ) {Δ} f = Bₑ Σ lem₁
  where
  lem₂ : Σ < q ∙> [] > [ Γ [ Δ ] ] ⊢NL _
  lem₂ rewrite sym (<>-def Σ (q ∙> []) (Γ [ Δ ])) = f
  lem₁ : Σ [ q ∙ (Δ ∘ λx Γ [x]) ] ⊢NL _
  lem₁ rewrite     (<>-def Σ (q ∙> []) (Δ ∘ λx Γ [x])) = down (Σ < q ∙> [] >) Γ lem₂
down Σ (Γ <∙ q) {Δ} f = Cₑ Σ lem₁
  where
  lem₂ : Σ < [] <∙ q > [ Γ [ Δ ] ] ⊢NL _
  lem₂ rewrite sym (<>-def Σ ([] <∙ q) (Γ [ Δ ])) = f
  lem₁ : Σ [ (Δ ∘ λx Γ [x]) ∙ q ] ⊢NL _
  lem₁ rewrite     (<>-def Σ ([] <∙ q) (Δ ∘ λx Γ [x])) = down (Σ < [] <∙ q >) Γ lem₂



-- Derived rules for scope taking

⇦Lλ : ∀ (Σ : Context) (Γ : Context₁) {p q r}
    → λx Γ [x] ⊢NL p → Σ [ · q · ] ⊢NL r → Σ [ Γ [ · q ⇦ p · ] ] ⊢NL r
⇦Lλ Σ Γ f g = up Σ Γ (⇦L Σ f g)


⇨Rλ : ∀ (Γ : Context₁) {p q}
    → Γ [ · p · ] ⊢NL q → λx Γ [x] ⊢NL p ⇨ q
⇨Rλ Γ f = ⇨R (down [] Γ f)


-- TODO: an attempt at deriving the rule for full parasitic scope
{-
para : ∀ (Σ : Context)
         (Γ₁ Γ₂ : Context₁) {Δ p q r}
         (pr : ∃ λ Δ → λx Γ₁ [x] ≡ Γ₂ [ Δ ])
     → λx Γ₂ [x] ⊢NL q
     → Σ [ Δ ∘ · p · ] ⊢NL r
     → Σ [ {!Γ₂ [ · p ⇦ q · ]!} ] ⊢NL r
para = {!!}
-}
