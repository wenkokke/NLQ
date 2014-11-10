------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Definitions categories and functors.
------------------------------------------------------------------------

module Categories where

open import Level
open import Algebra using (module Monoid; Monoid)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; zip)
open import Relation.Binary using (IsEquivalence; REL; Rel)
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

------------------------------------------------------------------------
--

record Category (o ℓ h : Level) : Set (suc (o ⊔ ℓ ⊔ h)) where
  infixr 7 _∙_
  infix  4 _≈_

  field
    Obj : Set o
    Hom : Rel Obj h
    ε   : ∀ {A}     → Hom A A
    _∙_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    _≈_ : ∀ {A B}   → Rel (Hom A B) ℓ

  field
    assoc         : ∀ {A B C D} {x : Hom C D} {y : Hom B C} {z : Hom A B}
                  → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))
    identityˡ     : ∀ {A B} {x : Hom A B}
                  → ε ∙ x ≈ x
    identityʳ     : ∀ {A B} {x : Hom A B}
                  → x ∙ ε ≈ x
    ∙-resp-≈      : ∀ {A B C} {x y : Hom B C} {z w : Hom A B}
                  → x ≈ y → z ≈ w → x ∙ z ≈ y ∙ w
    isEquivalence : ∀ {A B} → IsEquivalence (_≈_ {A} {B})


_[_,_] : ∀ {o ℓ h} (C : Category o ℓ h) (x y : Category.Obj C) → Set h
_[_,_] = Category.Hom

_[_≈_] : ∀ {o ℓ h} (C : Category o ℓ h) {x y : Category.Obj C} (f g : C [ x , y ]) → Set ℓ
_[_≈_] = Category._≈_

_[_∙_] : ∀ {o ℓ h} (C : Category o ℓ h) {x y z : Category.Obj C} (f : C [ y , z ]) (g : C [ x , y ]) → C [ x , z ]
_[_∙_] = Category._∙_


-- Define the category of monoids
Monoids : ∀ {c ℓ} → Monoid c ℓ → Category zero ℓ c
Monoids M = record
  { Obj           = ⊤
  ; Hom           = λ {tt tt → M.Carrier}
  ; ε             = M.ε
  ; _∙_           = M._∙_
  ; _≈_           = M._≈_
  ; assoc         = M.assoc _ _ _
  ; identityˡ     = proj₁ M.identity _
  ; identityʳ     = proj₂ M.identity _
  ; ∙-resp-≈      = M.∙-cong
  ; isEquivalence = M.isEquivalence
  }
  where
    module M = Monoid M


instance
  monoid→category′ : ∀ {c ℓ} {{M : Monoid c ℓ}} → Category zero ℓ c
  monoid→category′ {{M}} = Monoids M


-- Proof that types are categories
discrete : ∀ {ℓ} (A : Set ℓ) → Category _ _ _
discrete A = record
  { Obj           = A
  ; Hom           = λ _ _ → ⊤
  ; ε             = tt
  ; _∙_           = λ _ _ → tt
  ; _≈_           = _≡_
  ; assoc         = refl
  ; identityˡ     = refl
  ; identityʳ     = refl
  ; ∙-resp-≈      = λ _ _ → refl
  ; isEquivalence = P.isEquivalence
  }


-- Define the category of Agda Sets
Sets : ∀ o → Category _ _ _
Sets o = record
  { Obj           = Set o
  ; Hom           = λ x y → x → y
  ; ε             = λ x → x
  ; _∙_           = λ f g x → f (g x)
  ; _≈_           = λ f g → ∀ {x} → f x ≡ g x
  ; assoc         = refl
  ; identityˡ     = refl
  ; identityʳ     = refl
  ; ∙-resp-≈      = ∙-resp-≈
  ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
  }
  where
    ∙-resp-≈ : {A B C : Set o} {f₁ f₂ : B → C} {g₁ g₂ : A → B}
             → (∀ {x} → f₁ x ≡ f₂ x) → (∀ {x} → g₁ x ≡ g₂ x) → (∀ {x} → f₁ (g₁ x) ≡ f₂ (g₂ x))
    ∙-resp-≈ p₁ p₂ {x} rewrite p₂ {x} = p₁

    sym : {A B : Set o} {i j : A → B}
        → (∀ {x} → i x ≡ j x) → (∀ {x} → j x ≡ i x)
    sym f {x} rewrite f {x} = refl

    trans : {A B : Set o} {i j k : A → B}
          → (∀ {x} → i x ≡ j x) → (∀ {x} → j x ≡ k x) → (∀ {x} → i x ≡ k x)
    trans f g {x} rewrite f {x} | g {x} = refl


-- Proof that products are categories
product : ∀ {o₁ ℓ₁ h₁ o₂ ℓ₂ h₂} (C : Category o₁ ℓ₁ h₁) (D : Category o₂ ℓ₂ h₂)
          → Category (o₁ ⊔ o₂) (ℓ₁ ⊔ ℓ₂) (h₁ ⊔ h₂)
product C D = record
  { Obj           = C.Obj     ×     D.Obj
  ; Hom           = C.Hom -< _×_ >- D.Hom
  ; ε             = C.ε , D.ε
  ; _∙_           = zip C._∙_ D._∙_
  ; _≈_           = C._≈_ -< _×_ >- D._≈_
  ; assoc         = C.assoc     , D.assoc
  ; identityˡ     = C.identityˡ , D.identityˡ
  ; identityʳ     = C.identityʳ , D.identityʳ
  ; ∙-resp-≈      = zip C.∙-resp-≈ D.∙-resp-≈
  ; isEquivalence = C.isEquivalence ×-isEquivalence D.isEquivalence
  }
  where
    module C = Category C
    module D = Category D

    zipWith : ∀ {a b c p q r s} {A : Set a} {B : Set b} {C : Set c}
                {P : A → Set p} {Q : B → Set q} {R : C → Set r} {S : (x : C) → R x → Set s}
                (_∙_ : A → B → C) → (_∘_ : ∀ {x y} → P x → Q y → R (x ∙ y))
              → (_*_ : (x : C) → (y : R x) → S x y) → (x : Σ A P) → (y : Σ B Q)
              → S (proj₁ x ∙ proj₁ y) (proj₂ x ∘ proj₂ y)
    zipWith _∙_ _∘_ _*_ (a , p) (b , q) = (a ∙ b) * (p ∘ q)
    syntax zipWith f g h = f -< h >- g


[_×_] : ∀ {o₁ ℓ₁ h₁ o₂ ℓ₂ h₂} (C : Category o₁ ℓ₁ h₁) (D : Category o₂ ℓ₂ h₂)
      → Category (o₁ ⊔ o₂) (ℓ₁ ⊔ ℓ₂) (h₁ ⊔ h₂)
[_×_] = product


record Functor {o₁ ℓ₁ h₁ o₂ ℓ₂ h₂}
               (C : Category o₁ ℓ₁ h₁)
               (D : Category o₂ ℓ₂ h₂) :
               Set (o₁ ⊔ ℓ₁ ⊔ h₁ ⊔ o₂ ⊔ ℓ₂ ⊔ h₂) where

  private module C = Category C
  private module D = Category D

  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {x y} → C [ x , y ] → D [ F₀ x , F₀ y ]

  field
    identity     : ∀ {x}
                 → D [ F₁ (C.ε {x}) ≈ (D.ε {F₀ x}) ]
    homomorphism : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]}
                 → D [ F₁ (C [ g ∙ f ]) ≈ D [ F₁ g ∙ F₁ f ] ]
    F-resp-≈     : ∀ {x y} {f g : C [ x , y ]}
                 → C [ f ≈ g ] → D [ F₁ f ≈ F₁ g ]
