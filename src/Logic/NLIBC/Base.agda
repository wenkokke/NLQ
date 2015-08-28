------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Fin                                   using (Fin; suc; zero)
open import Data.Nat                                   using (ℕ; suc; zero)
open import Data.Nat.Properties.Simple as ℕ            using ()
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl; trans; cong; sym)


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

    ⇒ᴸ   : ∀ (Δ : Context) {Γ p q r}
         → Γ                   ⊢NL p
         → Δ [ · q · ]         ⊢NL r
         → Δ [ Γ ∙ · p ⇒ q · ] ⊢NL r

    ⇒ᴿ   : ∀ {Γ p q}
         → · p · ∙ Γ           ⊢NL q
         →         Γ           ⊢NL p ⇒ q

    ⇐ᴸ   : ∀ (Δ : Context) {Γ p q r}
         → Γ                   ⊢NL p
         → Δ [ · q · ]         ⊢NL r
         → Δ [ · q ⇐ p · ∙ Γ ] ⊢NL r

    ⇐ᴿ   : ∀ {Γ p q}
         → Γ ∙ · p ·           ⊢NL q
         → Γ                   ⊢NL q ⇐ p


    -- rules for (⇦, ∘, ⇨)

    ⇨ᴸ   : ∀ (Δ : Context) {Γ p q r}
         → Γ                   ⊢NL p
         → Δ [ · q · ]         ⊢NL r
         → Δ [ Γ ∘ · p ⇨ q · ] ⊢NL r

    ⇨ᴿ   : ∀ {Γ p q}
         → · p · ∘ Γ           ⊢NL q
         →         Γ           ⊢NL p ⇨ q

    ⇦ᴸ   : ∀ (Δ : Context) {Γ p q r}
         → Γ                   ⊢NL p
         → Δ [ · q · ]         ⊢NL r
         → Δ [ · q ⇦ p · ∘ Γ ] ⊢NL r

    ⇦ᴿ   : ∀ {Γ p q}
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

    ⇨ᴿgᴸ : ∀ (Γ : Context) {p q r}
         → Γ [ · q · ∙ p ] ⊢NL r
         → Γ [ p ] ⊢NL q ⇨ r

    ⇨ᴿgᴿ : ∀ (Γ : Context) {p q r}
         → Γ [ p ∙ · q · ] ⊢NL r
         → Γ [ p ] ⊢NL q ⇨ r


λx_[x] : (Γ : Context₁) → Structure
λx   []   [x] = I
λx p ∙> Γ [x] = (B ∙ p) ∙ λx Γ [x]
λx Γ <∙ r [x] = (C ∙ λx Γ [x]) ∙ r


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

⇦ᴸλ : ∀ (Σ : Context) (Γ : Context₁) {p q r}
    → λx Γ [x] ⊢NL p → Σ [ · q · ] ⊢NL r → Σ [ Γ [ · q ⇦ p · ] ] ⊢NL r
⇦ᴸλ Σ Γ f g = up Σ Γ (⇦ᴸ Σ f g)


⇨ᴿλ : ∀ (Γ : Context₁) {p q}
    → Γ [ · p · ] ⊢NL q → λx Γ [x] ⊢NL p ⇨ q
⇨ᴿλ Γ f = ⇨ᴿ (down [] Γ f)


-- Paths for contexts with multiple holes

private
  suc-inj : {m n : ℕ} → _≡_ {A = ℕ} (suc m) (suc n) → m ≡ n
  suc-inj refl = refl

λxᵢ_[xᵢ] : ∀ {i} (Γ : Contextᵢ (suc i)) → Contextᵢ i
λxᵢ var                        [xᵢ] = con I
λxᵢ dot {zero } {zero } () Γ Δ [xᵢ]
λxᵢ dot {suc m} {zero } pr Γ Δ [xᵢ]
  = dot (suc-inj pr) (dot refl (con C) λxᵢ Γ [xᵢ]) Δ
λxᵢ dot {    m} {suc n} pr Γ Δ [xᵢ]
  = dot (suc-inj (trans pr (ℕ.+-suc m n))) (dot refl (con B) Γ) λxᵢ Δ [xᵢ]


-- Minor correctness proof for the case where multi-hole linear contexts
-- have exactly one hole. In this case, λxᵢ_[xᵢ] corresponds to the much
-- easier to read function λx_[x].
λxᵢΓ[xᵢ]-correct : (Γ : Contextᵢ 1) → ⌊ λxᵢ Γ [xᵢ] ⌋₀ ≡ λx ⌊ Γ ⌋₁ [x]
λxᵢΓ[xᵢ]-correct  var                           = refl
λxᵢΓ[xᵢ]-correct (dot {zero       } {zero       } ()   Γ₁ Γ₂)
λxᵢΓ[xᵢ]-correct (dot {zero       } {suc zero   } refl Γ₁ Γ₂)
  rewrite λxᵢΓ[xᵢ]-correct Γ₂ = refl
λxᵢΓ[xᵢ]-correct (dot {zero       } {suc (suc _)} ()   Γ₁ Γ₂)
λxᵢΓ[xᵢ]-correct (dot {suc zero   } {zero       } refl Γ₁ Γ₂)
  rewrite λxᵢΓ[xᵢ]-correct Γ₁ = refl
λxᵢΓ[xᵢ]-correct (dot {suc (suc _)} {zero       } ()   Γ₁ Γ₂)
λxᵢΓ[xᵢ]-correct (dot {suc m      } {suc n      } pr   Γ₁ Γ₂)
  with trans pr (cong suc (ℕ.+-suc m n)) ; ... | ()

λx₁⋯xᵢ_[xᵢ]⋯[x₁] : ∀ {i} (Γ : Contextᵢ i) → Structure
λx₁⋯xᵢ_[xᵢ]⋯[x₁] {zero } Γ = ⌊ Γ ⌋₀
λx₁⋯xᵢ_[xᵢ]⋯[x₁] {suc i} Γ = λx₁⋯xᵢ λxᵢ Γ [xᵢ] [xᵢ]⋯[x₁]






-- TODO: an attempt at deriving the rule for full parasitic scope
{-
para : ∀ (Σ : Context) (Γ : Contextᵢ 2) {Δ p q r}
     → (i : Fin 2)
     → λx₁⋯xᵢ Γ [xᵢ]⋯[x₁] ⊢NL p
     → Σ [ Δ ∘ · q · ] ⊢NL r
     → Σ [ (Γ [ Δ ]₂ i) [ · q ⇦ p · ] ] ⊢NL r
para Σ (dot {0} {2} pr Γ₁ Γ₂) {Δ} {p} {q}i f g = h′
  where
    f′ : (B ∙ (B ∙ ⌊ Γ₁ ⌋₀)) ∙ ⌊ λxᵢ λxᵢ Γ₂ [xᵢ] [xᵢ] ⌋₀ ⊢NL _
    f′ = f
    g′ : Σ [ Δ ∘ · q · ] ⊢NL _
    g′ = g
    h′ : Σ [ _[_] {!!} · q ⇦ p · ] ⊢NL _
    -- (Γ₁ ∙> (Γ₂ [ Δ ]₂ i))
    h′ = {!!}
para Σ (dot {2} {0} pr Γ₁ Γ₂) {Δ} {p} {q} i f g = h′
  where
    f′ : (C ∙ ((B ∙ C) ∙ ⌊ λxᵢ λxᵢ Γ₁ [xᵢ] [xᵢ] ⌋₀)) ∙ ⌊ Γ₂ ⌋₀ ⊢NL _
    f′ = f
    g′ : Σ [ Δ ∘ · q · ] ⊢NL _
    g′ = g
    h′ : Σ [ (dot pr Γ₁ Γ₂ [ Δ ]₂ i) [ · q ⇦ p · ] ] ⊢NL _
    h′ = {!!}
para Σ (dot {1} {1} pr Γ₁ Γ₂) {Δ} {p} {q} zero f g = h′
  where
    f′ : (C ∙ ((B ∙ B) ∙ ⌊ λxᵢ Γ₁ [xᵢ] ⌋₀)) ∙ ⌊ λxᵢ Γ₂ [xᵢ] ⌋₀ ⊢NL _
    f′ = f
    g′ : Σ [ Δ ∘ · q · ] ⊢NL _
    g′ = g
    h′ : Σ [ (dot pr Γ₁ Γ₂ [ Δ ]₂ zero) [ · q ⇦ p · ] ] ⊢NL _
    h′ = {!!}
para Σ (dot {1} {1} pr Γ₁ Γ₂) {Δ} {p} {q} (suc zero) f g = h′
  where
    f′ : (C ∙ ((B ∙ B) ∙ ⌊ λxᵢ Γ₁ [xᵢ] ⌋₀)) ∙ ⌊ λxᵢ Γ₂ [xᵢ] ⌋₀ ⊢NL _
    f′ = f
    g′ : Σ [ Δ ∘ · q · ] ⊢NL _
    g′ = g
    h′ : Σ [ (dot pr Γ₁ Γ₂ [ Δ ]₂ suc zero) [ · q ⇦ p · ] ] ⊢NL _
    h′ = {!!}

para _ (dot {1                } {1                } pr _ _) (suc (suc ()))
para _ (dot {0                } {0                } () _ _)
para _ (dot {0                } {1                } () _ _)
para _ (dot {0                } {suc (suc (suc _))} () _ _)
para _ (dot {1                } {0                } () _ _)
para _ (dot {suc (suc (suc _))} {0                } () _ _)
para _ (dot {1                } {suc (suc _)      } () _ _)
para _ (dot {suc (suc m)      } {suc n            } pr _ _)
  with trans pr (cong suc (cong suc (ℕ.+-suc m n))) ; ... | ()
-}
