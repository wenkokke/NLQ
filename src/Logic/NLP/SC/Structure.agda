------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.NLP.SC.Structure {ℓ} (Atom : Set ℓ) where


open import Logic.NLP.SC.Type Atom


infixr 30 _∙_
infixl 50 _⋈ˢ

data Structure : Set ℓ where
  ·_·  : Type      → Structure
  ⟨_⟩  : Structure → Structure
  _∙_  : Structure → Structure → Structure
  L    : Structure
  R    : Structure


-- Proofs which show that constructors of types (as all Agda
-- data-constructors) respect equality.
··-injective : ∀ {p q} → · p · ≡ · q · → p ≡ q
··-injective refl = refl

⟨⟩-injective : ∀ {p q} → ⟨ p ⟩ ≡ ⟨ q ⟩ → p ≡ q
⟨⟩-injective refl = refl

∙-injective : ∀ {p₁ p₂ q₁ q₂} → p₁ ∙ q₁ ≡ p₂ ∙ q₂ → p₁ ≡ p₂ × q₁ ≡ q₂
∙-injective refl = refl , refl


_⋈ˢ : Structure → Structure
·  A  · ⋈ˢ = · A ⋈ᵗ ·
⟨  Γ  ⟩ ⋈ˢ = ⟨ Γ ⋈ˢ ⟩
(Γ ∙ Δ) ⋈ˢ = (Δ ⋈ˢ) ∙ (Γ ⋈ˢ)
L       ⋈ˢ = R
R       ⋈ˢ = L


open import Algebra.FunctionProperties {A = Structure} _≡_


⋈ˢ-inv : Involutive _⋈ˢ
⋈ˢ-inv · A · rewrite ⋈ᵗ-inv A = refl
⋈ˢ-inv ⟨ Γ ⟩ rewrite ⋈ˢ-inv Γ = refl
⋈ˢ-inv (Γ ∙ Δ) rewrite ⋈ˢ-inv Γ | ⋈ˢ-inv Δ = refl
⋈ˢ-inv L = refl
⋈ˢ-inv R = refl
