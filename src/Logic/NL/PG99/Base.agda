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


module Logic.NL.PG99.Base {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type           Atom as T
open import Logic.NL.Type.Context   Atom as C; open C.Simple using (_[_]; _<_>; <>-assoc; <>-def)
open import Logic.NL.PG99.Sequent Atom as J


infix 1 NL_ _⊢NL_ ⊢NLᴺ_ ⊢NLᴾ_

mutual
  _⊢NL_ : Type → Type → Set ℓ
  A ⊢NL B = NL A ⊢ B

  ⊢NLᴺ_ : Context → Set ℓ
  ⊢NLᴺ Γ = NL ⊢ᴺ Γ

  ⊢NLᴾ_ : Context → Set ℓ
  ⊢NLᴾ Δ = NL ⊢ᴾ Δ

  data NL_ : Sequent → Set ℓ where

    ax     : ∀ {A}       → el A ⊢NL el A
    m⊗     : ∀ {A B C D} → A ⊢NL B → C ⊢NL D → A ⊗ C ⊢NL B ⊗ D
    m⇒     : ∀ {A B C D} → A ⊢NL B → C ⊢NL D → B ⇒ C ⊢NL A ⇒ D
    m⇐     : ∀ {A B C D} → A ⊢NL B → C ⊢NL D → A ⇐ D ⊢NL B ⇐ C

    contᴺ  : ∀ {Γ A B A′} (f : A ⊢NL B) (x : ⊢NLᴺ Γ)
             (p₁  : A′ ≡ Γ [ A ]) (p₂ : False (Contᴺ? f)) (p₃ : False (is-[]? Γ))
             → A′ ⊢NL B
    contᴾ  : ∀ {Δ A B B′} (f : A ⊢NL B) (x : ⊢NLᴾ Δ)
             (p₁  : B′ ≡ Δ [ B ]) (p₂ : False (Contᴾ? f)) (p₃ : False (is-[]? Δ))
             → A ⊢NL B′

    neg-[] : ⊢NLᴺ []
    neg-⊗⇒ : ∀ {Γ Δ A B} → A ⊢NL B → ⊢NLᴺ Γ → ⊢NLᴺ Δ → ⊢NLᴺ A ⊗> Γ < B ⇒> Δ >
    neg-⊗⇐ : ∀ {Γ Δ A B} → A ⊢NL B → ⊢NLᴺ Γ → ⊢NLᴺ Δ → ⊢NLᴺ Γ < Δ <⇐ B > <⊗ A

    pos-[] : ⊢NLᴾ []
    pos-⇒⊗ : ∀ {Γ Δ A B} → A ⊢NL B → ⊢NLᴾ Γ → ⊢NLᴾ Δ → ⊢NLᴾ A ⇒> Γ < B ⊗> Δ >
    pos-⇐⊗ : ∀ {Γ Δ A B} → A ⊢NL B → ⊢NLᴾ Γ → ⊢NLᴾ Δ → ⊢NLᴾ Γ < Δ <⊗ B > <⇐ A
    pos-⇐⇒ : ∀ {Γ Δ B A} → B ⊢NL A → ⊢NLᴺ Γ → ⊢NLᴾ Δ → ⊢NLᴾ A ⇐> Γ < Δ <⇒ B >
    pos-⇒⇐ : ∀ {Γ Δ B A} → B ⊢NL A → ⊢NLᴺ Γ → ⊢NLᴾ Δ → ⊢NLᴾ Γ < B ⇐> Δ > <⇒ A


  data Contᴺ : ∀ {A B} (f : A ⊢NL B) → Set ℓ where
    contᴺ : ∀ {Γ A B A′} (f : A ⊢NL B) (x : ⊢NLᴺ Γ)
            (p₁ : A′ ≡ Γ [ A ]) (p₂ : False (Contᴺ? f)) (p₃ : False (is-[]? Γ))
          → Contᴺ (contᴺ f x p₁ p₂ p₃)

  Contᴺ? : ∀ {A B} (f : A ⊢NL B) → Dec (Contᴺ f)
  Contᴺ? ax = no (λ ())
  Contᴺ? (m⊗ _ _) = no (λ ())
  Contᴺ? (m⇒ _ _) = no (λ ())
  Contᴺ? (m⇐ _ _) = no (λ ())
  Contᴺ? (contᴺ f x p₁ p₂ p₃) = yes (contᴺ f x p₁ p₂ p₃)
  Contᴺ? (contᴾ _ _ _  _  _ ) = no (λ ())


  data Contᴾ : ∀ {A B} (f : A ⊢NL B) → Set ℓ where
    contᴾ : ∀ {Δ A B B′} (f : A ⊢NL B) (x : ⊢NLᴾ Δ)
            (p₁ : B′ ≡ Δ [ B ]) (p₂ : False (Contᴾ? f)) (p₃ : False (is-[]? Δ))
          → Contᴾ (contᴾ f x p₁ p₂ p₃)

  Contᴾ? : ∀ {A B} (f : A ⊢NL B) → Dec (Contᴾ f)
  Contᴾ? ax = no (λ ())
  Contᴾ? (m⊗ _ _) = no (λ ())
  Contᴾ? (m⇒ _ _) = no (λ ())
  Contᴾ? (m⇐ _ _) = no (λ ())
  Contᴾ? (contᴺ _ _ _  _  _ ) = no (λ ())
  Contᴾ? (contᴾ f x p₁ p₂ p₃) = yes (contᴾ f x p₁ p₂ p₃)


ax′ : ∀ {A} → A ⊢NL A
ax′ {el A}  = ax
ax′ {A ⊗ B} = m⊗ ax′ ax′
ax′ {A ⇒ B} = m⇒ ax′ ax′
ax′ {A ⇐ B} = m⇐ ax′ ax′


transᴺ′ : ∀ {Γ Δ} → ⊢NLᴺ Γ → ⊢NLᴺ Δ → ⊢NLᴺ Γ < Δ >
transᴺ′ neg-[] g = g
transᴺ′ {._} {Σ} (neg-⊗⇒ {Γ} {Δ} {A} {B} p f₁ f₂) g
  rewrite <>-assoc Γ (B ⇒> Δ) Σ = neg-⊗⇒ p f₁ (transᴺ′ f₂ g)
transᴺ′ {._} {Σ} (neg-⊗⇐ {Γ} {Δ} {A} {B} p f₁ f₂) g
  rewrite <>-assoc Γ (Δ <⇐ B) Σ = neg-⊗⇐ p f₁ (transᴺ′ f₂ g)


transᴾ′ : ∀ {Γ Δ} → ⊢NLᴾ Γ → ⊢NLᴾ Δ → ⊢NLᴾ Γ < Δ >
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
contᴺ′ : ∀ {Γ A B} → A ⊢NL B → ⊢NLᴺ Γ → Γ [ A ] ⊢NL B
contᴺ′ {Γ}  f x with is-[]? Γ | Contᴺ? f
contᴺ′ f neg-[] | yes refl | _      = f
contᴺ′ f x      | no ¬p₃   | no ¬p₂ =
  contᴺ f x refl (fromWitnessFalse ¬p₂) (fromWitnessFalse ¬p₃)
contᴺ′ {Γ} ._ x | no ¬p₃   | yes (contᴺ f y p₁ p₂ p₃) =
  contᴺ f (transᴺ′ x y) (lem-p₁ Γ p₁) p₂ (fromWitnessFalse (lem-p₃ Γ (toWitnessFalse p₃)))

-- Derived version of the contᴾ rule which ensures that the proof is normalised.
contᴾ′ : ∀ {Δ A B} → A ⊢NL B → ⊢NLᴾ Δ → A ⊢NL Δ [ B ]
contᴾ′ {Δ} f x with is-[]? Δ | Contᴾ? f
contᴾ′ f pos-[] | yes refl | _ = f
contᴾ′ f x      | no ¬p₃   | no ¬p₂ =
  contᴾ f x refl (fromWitnessFalse ¬p₂) (fromWitnessFalse ¬p₃)
contᴾ′ {Δ} ._ x | no ¬p₃   | yes (contᴾ f y p₁ p₂ p₃) =
  contᴾ f (transᴾ′ x y) (lem-p₁ Δ p₁) p₂ (fromWitnessFalse (lem-p₃ Δ (toWitnessFalse p₃)))


-- Admissible ⇒⊗ residuation rule (referred to as `e2` by de Grootte).
r⇒⊗′ : ∀ {A B C} → B ⊢NL A ⇒ C → A ⊗ B ⊢NL C
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
r⇐⊗′ : ∀ {A B C} → A ⊢NL C ⇐ B → A ⊗ B ⊢NL C
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
r⊗⇒′ : ∀ {A B C} → A ⊗ B ⊢NL C → B ⊢NL A ⇒ C
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
r⊗⇐′ : ∀ {A B C} → A ⊗ B ⊢NL C → A ⊢NL C ⇐ B
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




⊬ᴾA⊗>Δ : ∀ {A Δ} → ¬ (⊢NLᴾ A ⊗> Δ)
⊬ᴾA⊗>Δ ()

⊬ᴾΔ<⊗A : ∀ {A Δ} → ¬ (⊢NLᴾ Δ <⊗ A)
⊬ᴾΔ<⊗A ()

⊬ᴺA⇒>Γ : ∀ {A Γ} → ¬ (⊢NLᴺ A ⇒> Γ)
⊬ᴺA⇒>Γ ()

⊬ᴺA⇐>Γ : ∀ {A Γ} → ¬ (⊢NLᴺ A ⇐> Γ)
⊬ᴺA⇐>Γ ()

⊬ᴺΓ<⇒A : ∀ {A Γ} → ¬ (⊢NLᴺ Γ <⇒ A)
⊬ᴺΓ<⇒A ()

⊬ᴺΓ<⇐A : ∀ {A Γ} → ¬ (⊢NLᴺ Γ <⇐ A)
⊬ᴺΓ<⇐A ()
