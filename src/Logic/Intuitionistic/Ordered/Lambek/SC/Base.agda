------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements the axioms and some derived inference rules.
------------------------------------------------------------------------


open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse; toWitnessFalse)
open import Relation.Binary using (module DecSetoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl; sym)


module Logic.Intuitionistic.Ordered.Lambek.SC.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Ordered.Lambek.Type         Univ as T
open import Logic.Intuitionistic.Ordered.Lambek.Type.Context Univ as C
open import Logic.Intuitionistic.Ordered.Lambek.SC.Judgement Univ as J
open C.Simple using (_[_]; _<_>; <>-assoc; <>-def)


infix 1 NL_

mutual
  data NL_ : Judgement → Set ℓ where

    ax     : ∀ {A}       → NL el A ⊢ el A
    m⊗  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⊗ C ⊢ B ⊗ D
    m⇒  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL B ⇒ C ⊢ A ⇒ D
    m⇐  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⇐ D ⊢ B ⇐ C
    contᴺ  : ∀ {Γ A B A′} (f : NL A ⊢ B) (x : NL ⊢ᴺ Γ)
             (p₁  : A′ ≡ Γ [ A ]) (p₂ : False (Contᴺ? f)) (p₃ : False (is-[]? Γ))
             → NL A′ ⊢ B
    contᴾ  : ∀ {Δ A B B′} (f : NL A ⊢ B) (x : NL ⊢ᴾ Δ)
             (p₁  : B′ ≡ Δ [ B ]) (p₂ : False (Contᴾ? f)) (p₃ : False (is-[]? Δ))
             → NL A ⊢ B′

    neg-[] : NL ⊢ᴺ []
    neg-⊗⇒ : ∀ {Γ Δ A B} → NL A ⊢ B → NL ⊢ᴺ Γ → NL ⊢ᴺ Δ → NL ⊢ᴺ A ⊗> Γ < B ⇒> Δ >
    neg-⊗⇐ : ∀ {Γ Δ A B} → NL A ⊢ B → NL ⊢ᴺ Γ → NL ⊢ᴺ Δ → NL ⊢ᴺ Γ < Δ <⇐ B > <⊗ A

    pos-[] : NL ⊢ᴾ []
    pos-⇒⊗ : ∀ {Γ Δ A B} → NL A ⊢ B → NL ⊢ᴾ Γ → NL ⊢ᴾ Δ → NL ⊢ᴾ A ⇒> Γ < B ⊗> Δ >
    pos-⇐⊗ : ∀ {Γ Δ A B} → NL A ⊢ B → NL ⊢ᴾ Γ → NL ⊢ᴾ Δ → NL ⊢ᴾ Γ < Δ <⊗ B > <⇐ A
    pos-⇐⇒ : ∀ {Γ Δ B A} → NL B ⊢ A → NL ⊢ᴺ Γ → NL ⊢ᴾ Δ → NL ⊢ᴾ A ⇐> Γ < Δ <⇒ B >
    pos-⇒⇐ : ∀ {Γ Δ B A} → NL B ⊢ A → NL ⊢ᴺ Γ → NL ⊢ᴾ Δ → NL ⊢ᴾ Γ < B ⇐> Δ > <⇒ A


  data Contᴺ : ∀ {A B} (f : NL A ⊢ B) → Set ℓ where
    contᴺ : ∀ {Γ A B A′} (f : NL A ⊢ B) (x : NL ⊢ᴺ Γ)
            (p₁ : A′ ≡ Γ [ A ]) (p₂ : False (Contᴺ? f)) (p₃ : False (is-[]? Γ))
          → Contᴺ (contᴺ f x p₁ p₂ p₃)

  Contᴺ? : ∀ {A B} (f : NL A ⊢ B) → Dec (Contᴺ f)
  Contᴺ? ax = no (λ ())
  Contᴺ? (m⊗ _ _) = no (λ ())
  Contᴺ? (m⇒ _ _) = no (λ ())
  Contᴺ? (m⇐ _ _) = no (λ ())
  Contᴺ? (contᴺ f x p₁ p₂ p₃) = yes (contᴺ f x p₁ p₂ p₃)
  Contᴺ? (contᴾ _ _ _  _  _ ) = no (λ ())


  data Contᴾ : ∀ {A B} (f : NL A ⊢ B) → Set ℓ where
    contᴾ : ∀ {Δ A B B′} (f : NL A ⊢ B) (x : NL ⊢ᴾ Δ)
            (p₁ : B′ ≡ Δ [ B ]) (p₂ : False (Contᴾ? f)) (p₃ : False (is-[]? Δ))
          → Contᴾ (contᴾ f x p₁ p₂ p₃)

  Contᴾ? : ∀ {A B} (f : NL A ⊢ B) → Dec (Contᴾ f)
  Contᴾ? ax = no (λ ())
  Contᴾ? (m⊗ _ _) = no (λ ())
  Contᴾ? (m⇒ _ _) = no (λ ())
  Contᴾ? (m⇐ _ _) = no (λ ())
  Contᴾ? (contᴺ _ _ _  _  _ ) = no (λ ())
  Contᴾ? (contᴾ f x p₁ p₂ p₃) = yes (contᴾ f x p₁ p₂ p₃)


ax′ : ∀ {A} → NL A ⊢ A
ax′ {el A}  = ax
ax′ {A ⊗ B} = m⊗ ax′ ax′
ax′ {A ⇒ B} = m⇒ ax′ ax′
ax′ {A ⇐ B} = m⇐ ax′ ax′


transᴺ′ : ∀ {Γ Δ} → NL ⊢ᴺ Γ → NL ⊢ᴺ Δ → NL ⊢ᴺ Γ < Δ >
transᴺ′ neg-[] g = g
transᴺ′ {._} {Σ} (neg-⊗⇒ {Γ} {Δ} {A} {B} p f₁ f₂) g
  rewrite <>-assoc Γ (B ⇒> Δ) Σ = neg-⊗⇒ p f₁ (transᴺ′ f₂ g)
transᴺ′ {._} {Σ} (neg-⊗⇐ {Γ} {Δ} {A} {B} p f₁ f₂) g
  rewrite <>-assoc Γ (Δ <⇐ B) Σ = neg-⊗⇐ p f₁ (transᴺ′ f₂ g)


transᴾ′ : ∀ {Γ Δ} → NL ⊢ᴾ Γ → NL ⊢ᴾ Δ → NL ⊢ᴾ Γ < Δ >
transᴾ′ pos-[] g = g
transᴾ′ {._} {Σ} (pos-⇒⊗ {Γ} {Δ} {A} {B} p f₁ f₂) g
  rewrite <>-assoc Γ (B ⊗> Δ) Σ = pos-⇒⊗ p f₁ (transᴾ′ f₂ g)
transᴾ′ {._} {Σ} (pos-⇐⊗ {Γ} {Δ} {A} {B} p f₁ f₂) g
  rewrite <>-assoc Γ (Δ <⊗ B) Σ = pos-⇐⊗ p f₁ (transᴾ′ f₂ g)
transᴾ′ {._} {Σ} (pos-⇐⇒ {Γ} {Δ} {B} {A} p f₁ f₂) g
  rewrite <>-assoc Γ (Δ <⇒ B) Σ = pos-⇐⇒ p f₁ (transᴾ′ f₂ g)
transᴾ′ {._} {Σ} (pos-⇒⇐ {Γ} {Δ} {B} {A} p f₁ f₂) g
  rewrite <>-assoc Γ (B ⇐> Δ) Σ = pos-⇒⇐ p f₁ (transᴾ′ f₂ g)


private
  -- Lemma which combines several rewrite steps into a single function,
  -- used in the definitions of contᴺ′ and contᴾ′ below.
  lem-p₁ : ∀ {Γ} Δ {A A′} → A′ ≡ Γ [ A ] → Δ [ A′ ] ≡ (Δ < Γ >) [ A ]
  lem-p₁ {Γ} Δ {A} p rewrite p = sym (<>-def Δ Γ A)


  -- Lemma which shows that if a context is not empty, then the
  -- embedding of it in another (possibly empty) context is not empty
  -- either.
  lem-p₃ : ∀ {Γ} Δ → Γ ≢ [] → Δ < Γ > ≢ []
  lem-p₃ [] p = p
  lem-p₃ (_ ⊗> Δ) p = λ ()
  lem-p₃ (_ ⇒> Δ) p = λ ()
  lem-p₃ (_ ⇐> Δ) p = λ ()
  lem-p₃ (Δ <⊗ _) p = λ ()
  lem-p₃ (Δ <⇒ _) p = λ ()
  lem-p₃ (Δ <⇐ _) p = λ ()


-- Derived version of the contᴺ rule which ensures that the proof is normalised.
contᴺ′ : ∀ {Γ A B} → NL A ⊢ B → NL ⊢ᴺ Γ → NL Γ [ A ] ⊢ B
contᴺ′ {Γ}  f x with is-[]? Γ | Contᴺ? f
contᴺ′ f neg-[] | yes refl | _      = f
contᴺ′ f x      | no ¬p₃   | no ¬p₂ =
  contᴺ f x refl (fromWitnessFalse ¬p₂) (fromWitnessFalse ¬p₃)
contᴺ′ {Γ} ._ x | no ¬p₃   | yes (contᴺ f y p₁ p₂ p₃) =
  contᴺ f (transᴺ′ x y) (lem-p₁ Γ p₁) p₂ (fromWitnessFalse (lem-p₃ Γ (toWitnessFalse p₃)))

-- Derived version of the contᴾ rule which ensures that the proof is normalised.
contᴾ′ : ∀ {Δ A B} → NL A ⊢ B → NL ⊢ᴾ Δ → NL A ⊢ Δ [ B ]
contᴾ′ {Δ} f x with is-[]? Δ | Contᴾ? f
contᴾ′ f pos-[] | yes refl | _ = f
contᴾ′ f x      | no ¬p₃   | no ¬p₂ =
  contᴾ f x refl (fromWitnessFalse ¬p₂) (fromWitnessFalse ¬p₃)
contᴾ′ {Δ} ._ x | no ¬p₃   | yes (contᴾ f y p₁ p₂ p₃) =
  contᴾ f (transᴾ′ x y) (lem-p₁ Δ p₁) p₂ (fromWitnessFalse (lem-p₃ Δ (toWitnessFalse p₃)))


-- Admissible ⇒⊗ residuation rule (referred to as `e2` by de Grootte).
r⇒⊗′ : ∀ {A B C} → NL B ⊢ A ⇒ C → NL A ⊗ B ⊢ C
r⇒⊗′ (m⇒ f g) = contᴺ′ g (neg-⊗⇒ f neg-[] neg-[])
r⇒⊗′ (contᴾ f pos-[] p₁ p₂ ())
r⇒⊗′ (contᴾ {._} {C} {D} f (pos-⇒⊗ {Γ} {Δ} {A} {B} g x y) p₁ p₂ p₃)
  rewrite proj₁ (⇒-injective p₁)
        | proj₂ (⇒-injective p₁)
        | <>-def Γ (B ⊗> Δ) D
        = contᴾ′ (m⊗ g (contᴾ′ f y)) x
r⇒⊗′ (contᴾ f (pos-⇐⊗ g x y) () p₂ p₃)
r⇒⊗′ (contᴾ f (pos-⇐⇒ g x y) () p₂ p₃)
r⇒⊗′ (contᴾ {._} {._} {C} f (pos-⇒⇐ {Γ} {Δ} {A} {B} g x y) p₁ p₂ p₃)
  rewrite proj₁ (⇒-injective p₁)
        | proj₂ (⇒-injective p₁)
        | <>-def Γ (A ⇐> Δ) C
        | sym (<>-def Γ ([] <⇐ Δ [ C ]) A)
        = contᴺ′ g (neg-⊗⇐ (contᴾ′ f y) x neg-[])
r⇒⊗′ (contᴺ {Γ} (m⇒ {A} {B} {C} {D} f g) x p₁ p₂ p₃)
  rewrite p₁ | sym (<>-def Γ (B ⇒> []) C)
        = contᴺ′ g (neg-⊗⇒ f x neg-[])
r⇒⊗′ (contᴺ (contᴺ f x p₁ p₂ p₃) x₁ p₄ () p₆)
r⇒⊗′ (contᴺ (contᴾ f pos-[] p₁ p₂ ()) x₁ p₄ p₅ p₆)
r⇒⊗′ (contᴺ (contᴾ {._} {C} {D} f (pos-⇒⊗ {Γ} {Δ} {A} {B} g y z) p₁ p₂ p₃) x p₄ p₅ p₆)
  rewrite p₄ | proj₁ (⇒-injective p₁) | proj₂ (⇒-injective p₁)
        | <>-def Γ (B ⊗> Δ) D
        = contᴾ′ (m⊗ g (contᴾ′ (contᴺ′ f x) z)) y
r⇒⊗′ (contᴺ (contᴾ f (pos-⇐⊗ f₁ x x₁) () p₂ p₃) x₂ p₄ p₅ p₆)
r⇒⊗′ (contᴺ (contᴾ f (pos-⇐⇒ f₁ x x₁) () p₂ p₃) x₂ p₄ p₅ p₆)
r⇒⊗′ (contᴺ (contᴾ {._} {._} {C} f (pos-⇒⇐ {Γ} {Δ} {A} {B} g y z) p₁ p₂ p₃) x p₄ p₅ p₆)
  rewrite p₄ | proj₁ (⇒-injective p₁) | proj₂ (⇒-injective p₁)
        | <>-def Γ (A ⇐> Δ) C
        | sym (<>-def Γ ([] <⇐ Δ [ C ]) A)
        = contᴺ′ g (neg-⊗⇐ (contᴾ′ (contᴺ′ f x) z) y neg-[])


-- Admissible ⇐⊗ residuation rule (referred to as `f2` by de Grootte).
r⇐⊗′ : ∀ {A B C} → NL A ⊢ C ⇐ B → NL A ⊗ B ⊢ C
r⇐⊗′ (m⇐ f g) = contᴺ′ f (neg-⊗⇐ g neg-[] neg-[])
r⇐⊗′ (contᴾ f pos-[] p₁ p₂ ())
r⇐⊗′ (contᴾ f (pos-⇒⊗ g x y) () p₂ p₃)
r⇐⊗′ (contᴾ {._} {._} {C} f (pos-⇐⊗ {Γ} {Δ} {A} {B} g x y) p₁ p₂ p₃)
  rewrite proj₁ (⇐-injective p₁)
        | proj₂ (⇐-injective p₁)
        | <>-def Γ (Δ <⊗ B) C
        = contᴾ′ (m⊗ (contᴾ′ f y) g) x
r⇐⊗′ (contᴾ {._} {._} {C} f (pos-⇐⇒ {Γ} {Δ} {A} {B} g x y) p₁ p₂ p₃)
  rewrite proj₁ (⇐-injective p₁)
        | proj₂ (⇐-injective p₁)
        | <>-def Γ (Δ <⇒ A) C
        | sym (<>-def Γ (Δ [ C ] ⇒> []) A)
        = contᴺ′ g (neg-⊗⇒ (contᴾ′ f y) x neg-[])
r⇐⊗′ (contᴾ f (pos-⇒⇐ g x y) () p₂ p₃)
r⇐⊗′ (contᴺ {Γ} (m⇐ {A} {B} {C} {D} f g) x p₁ p₂ p₃)
  rewrite p₁ | sym (<>-def Γ ([] <⇐ D) A)
        = contᴺ′ f (neg-⊗⇐ g x neg-[])
r⇐⊗′ (contᴺ (contᴺ f x p₁ p₂ p₃) x₁ p₄ () p₆)
r⇐⊗′ (contᴺ (contᴾ f pos-[] p₁ p₂ ()) x p₄ p₅ p₆)
r⇐⊗′ (contᴺ (contᴾ f (pos-⇒⊗ g y z) () p₂ p₃) x p₄ p₅ p₆)
r⇐⊗′ (contᴺ (contᴾ {._} {._} {C} f (pos-⇐⊗ {Γ} {Δ} {A} {B} g y z) p₁ p₂ p₃) x p₄ p₅ p₆)
  rewrite p₄ | proj₁ (⇐-injective p₁)
             | proj₂ (⇐-injective p₁)
             | <>-def Γ (Δ <⊗ B) C
             = contᴾ′ (m⊗ (contᴾ′ (contᴺ′ f x) z) g) y
r⇐⊗′ (contᴺ (contᴾ {._} {._} {C} f (pos-⇐⇒ {Γ} {Δ} {A} {B} g y z) p₁ p₂ p₃) x p₄ p₅ p₆)
  rewrite p₄ | proj₁ (⇐-injective p₁)
             | proj₂ (⇐-injective p₁)
             | <>-def Γ (Δ <⇒ A) C
             | sym (<>-def Γ (Δ [ C ] ⇒> []) A)
             = contᴺ′ g (neg-⊗⇒ (contᴾ′ (contᴺ′ f x) z) y neg-[])
r⇐⊗′ (contᴺ (contᴾ f (pos-⇒⇐ g y z) () p₂ p₃) x p₄ p₅ p₆)


-- Admissible ⊗⇒ residuation rule (referred to as `e1` by de Grootte).
r⊗⇒′ : ∀ {A B C} → NL A ⊗ B ⊢ C → NL B ⊢ A ⇒ C
r⊗⇒′ (m⊗ f g) = contᴾ′ g (pos-⇒⊗ f pos-[] pos-[])
r⊗⇒′ (contᴺ f neg-[] p₁ p₂ ())
r⊗⇒′ (contᴺ {._} {C} {D} f (neg-⊗⇒ {Γ} {Δ} {A} {B} g x y) p₁ p₂ p₃)
  rewrite proj₁ (⊗-injective p₁)
        | proj₂ (⊗-injective p₁)
        | <>-def Γ (B ⇒> Δ) C
        = contᴺ′ (m⇒ g (contᴺ′ f y)) x
r⊗⇒′ (contᴺ {._} {C} {D} f (neg-⊗⇐ {Γ} {Δ} {A} {B} g x y) p₁ p₂ p₃)
  rewrite proj₁ (⊗-injective p₁)
        | proj₂ (⊗-injective p₁)
        | <>-def Γ (Δ <⇐ B) C
        | sym (<>-def Γ (Δ [ C ] ⇐> []) B)
        = contᴾ′ g (pos-⇒⇐ (contᴺ′ f y) x pos-[])
r⊗⇒′ (contᴾ {Δ} (m⊗ {A} {B} {C} {D} f g) x p₁ p₂ p₃)
  rewrite p₁ | sym (<>-def Δ (B ⊗> []) D)
        = contᴾ′ g (pos-⇒⊗ f x pos-[])
r⊗⇒′ (contᴾ (contᴺ f neg-[] p₁ p₂ ()) x p₄ p₅ p₆)
r⊗⇒′ (contᴾ (contᴺ {._} {C} {D} f (neg-⊗⇒ {Γ} {Δ} {A} {B} g y z) p₁ p₂ p₃) x p₄ p₅ p₆)
  rewrite p₄ | proj₁ (⊗-injective p₁)
             | proj₂ (⊗-injective p₁)
             | <>-def Γ (B ⇒> Δ) C
             = contᴺ′ (m⇒ g (contᴺ′ (contᴾ′ f x) z)) y
r⊗⇒′ (contᴾ (contᴺ {._} {C} {D} f (neg-⊗⇐ {Γ} {Δ} {A} {B} g y z) p₁ p₂ p₃) x p₄ p₅ p₆)
  rewrite p₄ | proj₁ (⊗-injective p₁)
             | proj₂ (⊗-injective p₁)
             | <>-def Γ (Δ <⇐ B) C
             | sym (<>-def Γ (Δ [ C ] ⇐> []) B)
             = contᴾ′ g (pos-⇒⇐ (contᴺ′ (contᴾ′ f x) z) y pos-[])
r⊗⇒′ (contᴾ (contᴾ f y p₁ p₂ p₃) x p₄ () p₆)


-- Admissible ⊗⇐ residuation rule (referred to as `f1` by de Grootte).
r⊗⇐′ : ∀ {A B C} → NL A ⊗ B ⊢ C → NL A ⊢ C ⇐ B
r⊗⇐′ (m⊗ f g) = contᴾ′ f (pos-⇐⊗ g pos-[] pos-[])
r⊗⇐′ (contᴺ f neg-[] p₁ p₂ ())
r⊗⇐′ (contᴺ {._} {C} {D} f (neg-⊗⇒ {Γ} {Δ} {A} {B} g x y) p₁ p₂ p₃)
  rewrite proj₁ (⊗-injective p₁)
        | proj₂ (⊗-injective p₁)
        | <>-def Γ (B ⇒> Δ) C
        | sym (<>-def Γ ([] <⇒ Δ [ C ]) B)
        = contᴾ′ g (pos-⇐⇒ (contᴺ′ f y) x pos-[])
r⊗⇐′ (contᴺ {._} {C} {D} f (neg-⊗⇐ {Γ} {Δ} {A} {B} g x y) p₁ p₂ p₃)
  rewrite proj₁ (⊗-injective p₁)
        | proj₂ (⊗-injective p₁)
        | <>-def Γ (Δ <⇐ B) C
        = contᴺ′ (m⇐ (contᴺ′ f y) g) x
r⊗⇐′ {A} {B} (contᴾ {Δ} (m⊗ {._} {C} {._} {D} f g) x p₁ p₂ p₃)
  rewrite p₁ | sym (<>-def Δ ([] <⊗ D) C)
        = contᴾ′ f (pos-⇐⊗ g x pos-[])
r⊗⇐′ (contᴾ (contᴺ f neg-[] refl p₂ ()) x p₄ p₅ p₆)
r⊗⇐′ (contᴾ (contᴺ {._} {C} {D} f (neg-⊗⇒ {Γ} {Δ} {A} {B} g y z) p₁ p₂ p₃) x p₄ p₅ p₆)
  rewrite p₄ | proj₁ (⊗-injective p₁)
             | proj₂ (⊗-injective p₁)
             | <>-def Γ (B ⇒> Δ) C
             | sym (<>-def Γ ([] <⇒ Δ [ C ]) B)
             = contᴾ′ g (pos-⇐⇒ (contᴺ′ (contᴾ′ f x) z) y pos-[])
r⊗⇐′ (contᴾ (contᴺ {._} {C} {D} f (neg-⊗⇐ {Γ} {Δ} {A} {B} g y z) p₁ p₂ p₃) x p₄ p₅ p₆)
  rewrite p₄ | proj₁ (⊗-injective p₁)
             | proj₂ (⊗-injective p₁)
             | <>-def Γ (Δ <⇐ B) C
             = contᴺ′ (m⇐ (contᴺ′ (contᴾ′ f x) z) g) y
r⊗⇐′ (contᴾ (contᴾ f y p₁ p₂ p₃) x p₄ () p₆)




⊬ᴾA⊗>Δ : ∀ {A Δ} → ¬ (NL ⊢ᴾ A ⊗> Δ)
⊬ᴾA⊗>Δ ()

⊬ᴾΔ<⊗A : ∀ {A Δ} → ¬ (NL ⊢ᴾ Δ <⊗ A)
⊬ᴾΔ<⊗A ()

⊬ᴺA⇒>Γ : ∀ {A Γ} → ¬ (NL ⊢ᴺ A ⇒> Γ)
⊬ᴺA⇒>Γ ()

⊬ᴺA⇐>Γ : ∀ {A Γ} → ¬ (NL ⊢ᴺ A ⇐> Γ)
⊬ᴺA⇐>Γ ()

⊬ᴺΓ<⇒A : ∀ {A Γ} → ¬ (NL ⊢ᴺ Γ <⇒ A)
⊬ᴺΓ<⇒A ()

⊬ᴺΓ<⇐A : ∀ {A Γ} → ¬ (NL ⊢ᴺ Γ <⇐ A)
⊬ᴺΓ<⇐A ()
