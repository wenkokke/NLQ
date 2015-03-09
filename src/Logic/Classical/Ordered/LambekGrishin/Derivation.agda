------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function                                   using (_∘_; flip)
open import Categories.Category                        using (Category)
open import Categories.Functor                         using (Functor)
open import Categories.Agda                            using (Sets)
open import Data.List                                  using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum                                   using (_⊎_; inj₁; inj₂)
open import Data.Product                               using (∃; _×_; _,_)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Nullary.Decidable                 using (True; toWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; cong)


module Logic.Classical.Ordered.LambekGrishin.Derivation {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Base                Univ
open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised      Univ
open import Logic.Classical.Ordered.LambekGrishin.Type                PolarisedUniv
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised PolarisedUniv
open import Logic.Classical.Ordered.LambekGrishin.Judgement           PolarisedUniv




infix 1 LG_⋯_

data LG_⋯_ (I : Judgement) : (J : Judgement) → Set ℓ where

  []  : LG I ⋯ I

  ⇁   : ∀ {X A} {p : True (Negative? A)} → LG I ⋯ X ⊢ · A · → LG I ⋯ X ⊢[  A  ]
  ↽   : ∀ {X A} {p : True (Positive? A)} → LG I ⋯  · A · ⊢ X → LG I ⋯ [  A  ]⊢ X
  ⇀   : ∀ {X A} {p : True (Positive? A)} → LG I ⋯ X ⊢[  A  ] → LG I ⋯ X ⊢ · A ·
  ↼   : ∀ {X A} {p : True (Negative? A)} → LG I ⋯ [  A  ]⊢ X → LG I ⋯  · A · ⊢ X

  -- rules for (□ , ◇)
  ◇ᴸ  : ∀ {Y A} → LG I ⋯ ⟨ · A · ⟩ ⊢ Y → LG I ⋯ · ◇ A · ⊢ Y
  ◇ᴿ  : ∀ {X B} → LG I ⋯ X ⊢[ B ] → LG I ⋯ ⟨ X ⟩ ⊢[ ◇ B ]
  □ᴸ  : ∀ {A Y} → LG I ⋯ [ A ]⊢ Y → LG I ⋯ [ □ A ]⊢ [ Y ]
  □ᴿ  : ∀ {X A} → LG I ⋯ X ⊢ [ · A · ] → LG I ⋯ X ⊢   · □ A ·
  r□◇ : ∀ {X Y} → LG I ⋯ X ⊢ [ Y ] → LG I ⋯ ⟨ X ⟩ ⊢ Y
  r◇□ : ∀ {X Y} → LG I ⋯ ⟨ X ⟩ ⊢ Y → LG I ⋯ X ⊢ [ Y ]

  -- rules for (₀ , ⁰ , ₁ , ¹)
  ₀ᴸ  : ∀ {X A} → LG I ⋯ X  ⊢[ A ] → LG I ⋯ [ ₀ A ]⊢  ₀ X
  ₀ᴿ  : ∀ {X A} → LG I ⋯ X ⊢ ₀ · A · → LG I ⋯ X ⊢ · ₀ A ·
  ⁰ᴸ  : ∀ {X A} → LG I ⋯   X ⊢[ A ] → LG I ⋯ [ A ⁰ ]⊢  X ⁰
  ⁰ᴿ  : ∀ {X A} → LG I ⋯ X ⊢ · A · ⁰ → LG I ⋯ X ⊢ · A ⁰ ·
  ₁ᴸ  : ∀ {Y A} → LG I ⋯ ₁ · A · ⊢ Y → LG I ⋯ · ₁ A · ⊢ Y
  ₁ᴿ  : ∀ {Y A} → LG I ⋯ [ A ]⊢ Y → LG I ⋯ ₁ Y  ⊢[ ₁ A ]
  ¹ᴸ  : ∀ {Y A} → LG I ⋯ · A · ¹ ⊢ Y → LG I ⋯ · A ¹ · ⊢ Y
  ¹ᴿ  : ∀ {Y A} → LG I ⋯ [ A ]⊢ Y → LG I ⋯ Y ¹  ⊢[ A ¹ ]
  r⁰₀ : ∀ {X Y} → LG I ⋯ X ⊢ Y ⁰ → LG I ⋯ Y ⊢ ₀ X
  r₀⁰ : ∀ {X Y} → LG I ⋯ Y ⊢ ₀ X → LG I ⋯ X ⊢ Y ⁰
  r¹₁ : ∀ {X Y} → LG I ⋯ X ¹ ⊢ Y → LG I ⋯ ₁ Y ⊢ X
  r₁¹ : ∀ {X Y} → LG I ⋯ ₁ Y ⊢ X → LG I ⋯ X ¹ ⊢ Y

  -- rules for (⇐ , ⊗ , ⇒)
  ⊗ᴿ₁ : ∀ {X Y A B} → LG I ⋯ X ⊢[ A ] → LG Y ⊢[ B ] → LG I ⋯ X ⊗ Y ⊢[ A ⊗ B ]
  ⊗ᴿ₂ : ∀ {X Y A B} → LG X ⊢[ A ] → LG I ⋯ Y ⊢[ B ] → LG I ⋯ X ⊗ Y ⊢[ A ⊗ B ]
  ⊗ᴸ  : ∀ {Y   A B} → LG I ⋯ · A · ⊗ · B · ⊢ Y → LG I ⋯ · A ⊗ B · ⊢ Y
  ⇒ᴿ  : ∀ {X   A B} → LG I ⋯ X ⊢ · A · ⇒ · B · → LG I ⋯ X ⊢ · A ⇒ B ·
  ⇒ᴸ₁ : ∀ {X Y A B} → LG I ⋯ X ⊢[ A ] → LG [ B ]⊢ Y → LG I ⋯ [ A ⇒ B ]⊢ X ⇒ Y
  ⇒ᴸ₂ : ∀ {X Y A B} → LG X ⊢[ A ] → LG I ⋯ [ B ]⊢ Y → LG I ⋯ [ A ⇒ B ]⊢ X ⇒ Y
  ⇐ᴿ  : ∀ {X   A B} → LG I ⋯ X ⊢ · B · ⇐ · A · → LG I ⋯ X ⊢ · B ⇐ A ·
  ⇐ᴸ₁ : ∀ {X Y A B} → LG I ⋯ X ⊢[ A ] → LG [ B ]⊢ Y → LG I ⋯ [ B ⇐ A ]⊢ Y ⇐ X
  ⇐ᴸ₂ : ∀ {X Y A B} → LG X ⊢[ A ] → LG I ⋯ [ B ]⊢ Y → LG I ⋯ [ B ⇐ A ]⊢ Y ⇐ X
  r⇒⊗ : ∀ {X Y Z} → LG I ⋯ Y ⊢ X ⇒ Z → LG I ⋯ X ⊗ Y ⊢ Z
  r⊗⇒ : ∀ {X Y Z} → LG I ⋯ X ⊗ Y ⊢ Z → LG I ⋯ Y ⊢ X ⇒ Z
  r⇐⊗ : ∀ {X Y Z} → LG I ⋯ X ⊢ Z ⇐ Y → LG I ⋯ X ⊗ Y ⊢ Z
  r⊗⇐ : ∀ {X Y Z} → LG I ⋯ X ⊗ Y ⊢ Z → LG I ⋯ X ⊢ Z ⇐ Y

  -- residuation rules for (⇚ , ⊕ , ⇛)
  ⊕ᴸ₁ : ∀ {X Y A B} → LG I ⋯ [ B ]⊢ Y → LG [ A ]⊢ X → LG I ⋯ [ B ⊕ A ]⊢ Y ⊕ X
  ⊕ᴸ₂ : ∀ {X Y A B} → LG [ B ]⊢ Y → LG I ⋯ [ A ]⊢ X → LG I ⋯ [ B ⊕ A ]⊢ Y ⊕ X
  ⊕ᴿ  : ∀ {X A B} → LG I ⋯ X ⊢ · B · ⊕ · A · → LG I ⋯ X ⊢ · B ⊕ A ·
  ⇚ᴸ  : ∀ {X A B} → LG I ⋯ · A · ⇚ · B · ⊢ X → LG I ⋯ · A ⇚ B · ⊢ X
  ⇚ᴿ₁ : ∀ {X Y A B} → LG I ⋯ X ⊢[ A ] → LG [ B ]⊢ Y → LG I ⋯ X ⇚ Y ⊢[ A ⇚ B ]
  ⇚ᴿ₂ : ∀ {X Y A B} → LG X ⊢[ A ] → LG I ⋯ [ B ]⊢ Y → LG I ⋯ X ⇚ Y ⊢[ A ⇚ B ]
  ⇛ᴸ  : ∀ {X A B} → LG I ⋯ · B · ⇛ · A · ⊢ X → LG I ⋯ · B ⇛ A · ⊢ X
  ⇛ᴿ₁ : ∀ {X Y A B} → LG I ⋯ X ⊢[ A ] → LG [ B ]⊢ Y → LG I ⋯ Y ⇛ X ⊢[ B ⇛ A ]
  ⇛ᴿ₂ : ∀ {X Y A B} → LG X ⊢[ A ] → LG I ⋯ [ B ]⊢ Y → LG I ⋯ Y ⇛ X ⊢[ B ⇛ A ]
  r⇚⊕ : ∀ {X Y Z} → LG I ⋯ Z ⇚ X ⊢ Y → LG I ⋯ Z ⊢ Y ⊕ X
  r⊕⇚ : ∀ {X Y Z} → LG I ⋯ Z ⊢ Y ⊕ X → LG I ⋯ Z ⇚ X ⊢ Y
  r⇛⊕ : ∀ {X Y Z} → LG I ⋯ Y ⇛ Z ⊢ X → LG I ⋯ Z ⊢ Y ⊕ X
  r⊕⇛ : ∀ {X Y Z} → LG I ⋯ Z ⊢ Y ⊕ X → LG I ⋯ Y ⇛ Z ⊢ X

  -- grishin interaction principes
  d⇛⇐ : ∀ {X Y Z W} → LG I ⋯ X ⊗ Y ⊢ Z ⊕ W → LG I ⋯ Z ⇛ X ⊢ W ⇐ Y
  d⇛⇒ : ∀ {X Y Z W} → LG I ⋯ X ⊗ Y ⊢ Z ⊕ W → LG I ⋯ Z ⇛ Y ⊢ X ⇒ W
  d⇚⇒ : ∀ {X Y Z W} → LG I ⋯ X ⊗ Y ⊢ Z ⊕ W → LG I ⋯ Y ⇚ W ⊢ X ⇒ Z
  d⇚⇐ : ∀ {X Y Z W} → LG I ⋯ X ⊗ Y ⊢ Z ⊕ W → LG I ⋯ X ⇚ W ⊢ Z ⇐ Y


module Simple where

  apply : ∀ {I J} → LG I ⋯ J → LG I → LG J
  apply []        x = x
  apply (⇁ {p = p} f) x = ⇁ {p = p} (apply f x)
  apply (↽ {p = p} f) x = ↽ {p = p} (apply f x)
  apply (⇀ {p = p} f) x = ⇀ {p = p} (apply f x)
  apply (↼ {p = p} f) x = ↼ {p = p} (apply f x)
  apply (◇ᴸ  f  ) x = ◇ᴸ   (apply f x)
  apply (◇ᴿ  f  ) x = ◇ᴿ   (apply f x)
  apply (□ᴸ  f  ) x = □ᴸ   (apply f x)
  apply (□ᴿ  f  ) x = □ᴿ   (apply f x)
  apply (r□◇ f  ) x = r□◇  (apply f x)
  apply (r◇□ f  ) x = r◇□  (apply f x)
  apply (₀ᴸ  f  ) x = ₀ᴸ   (apply f x)
  apply (₀ᴿ  f  ) x = ₀ᴿ   (apply f x)
  apply (⁰ᴸ  f  ) x = ⁰ᴸ   (apply f x)
  apply (⁰ᴿ  f  ) x = ⁰ᴿ   (apply f x)
  apply (₁ᴸ  f  ) x = ₁ᴸ   (apply f x)
  apply (₁ᴿ  f  ) x = ₁ᴿ   (apply f x)
  apply (¹ᴸ  f  ) x = ¹ᴸ   (apply f x)
  apply (¹ᴿ  f  ) x = ¹ᴿ   (apply f x)
  apply (r⁰₀ f  ) x = r⁰₀  (apply f x)
  apply (r₀⁰ f  ) x = r₀⁰  (apply f x)
  apply (r¹₁ f  ) x = r¹₁  (apply f x)
  apply (r₁¹ f  ) x = r₁¹  (apply f x)
  apply (⊗ᴿ₁ f g) x = ⊗ᴿ   (apply f x) g
  apply (⊗ᴿ₂ f g) x = ⊗ᴿ f (apply g x)
  apply (⊗ᴸ  f  ) x = ⊗ᴸ   (apply f x)
  apply (⇒ᴿ  f  ) x = ⇒ᴿ   (apply f x)
  apply (⇒ᴸ₁ f g) x = ⇒ᴸ   (apply f x) g
  apply (⇒ᴸ₂ f g) x = ⇒ᴸ f (apply g x)
  apply (⇐ᴿ  f  ) x = ⇐ᴿ   (apply f x)
  apply (⇐ᴸ₁ f g) x = ⇐ᴸ   (apply f x) g
  apply (⇐ᴸ₂ f g) x = ⇐ᴸ f (apply g x)
  apply (r⇒⊗ f  ) x = r⇒⊗  (apply f x)
  apply (r⊗⇒ f  ) x = r⊗⇒  (apply f x)
  apply (r⇐⊗ f  ) x = r⇐⊗  (apply f x)
  apply (r⊗⇐ f  ) x = r⊗⇐  (apply f x)
  apply (⊕ᴸ₁ f g) x = ⊕ᴸ   (apply f x) g
  apply (⊕ᴸ₂ f g) x = ⊕ᴸ f (apply g x)
  apply (⊕ᴿ  f  ) x = ⊕ᴿ   (apply f x)
  apply (⇚ᴸ  f  ) x = ⇚ᴸ   (apply f x)
  apply (⇚ᴿ₁ f g) x = ⇚ᴿ   (apply f x) g
  apply (⇚ᴿ₂ f g) x = ⇚ᴿ f (apply g x)
  apply (⇛ᴸ  f  ) x = ⇛ᴸ   (apply f x)
  apply (⇛ᴿ₁ f g) x = ⇛ᴿ   (apply f x) g
  apply (⇛ᴿ₂ f g) x = ⇛ᴿ f (apply g x)
  apply (r⇚⊕ f  ) x = r⇚⊕  (apply f x)
  apply (r⊕⇚ f  ) x = r⊕⇚  (apply f x)
  apply (r⇛⊕ f  ) x = r⇛⊕  (apply f x)
  apply (r⊕⇛ f  ) x = r⊕⇛  (apply f x)
  apply (d⇛⇐ f  ) x = d⇛⇐  (apply f x)
  apply (d⇛⇒ f  ) x = d⇛⇒  (apply f x)
  apply (d⇚⇒ f  ) x = d⇚⇒  (apply f x)
  apply (d⇚⇐ f  ) x = d⇚⇐  (apply f x)

  compose : ∀ {I J K} → LG J ⋯ K → LG I ⋯ J → LG I ⋯ K
  compose [] f = f
  compose (⇁ {p = p} g) f = ⇁ {p = p} (compose g f)
  compose (↽ {p = p} g) f = ↽ {p = p} (compose g f)
  compose (⇀ {p = p} g) f = ⇀ {p = p} (compose g f)
  compose (↼ {p = p} g) f = ↼ {p = p} (compose g f)
  compose (◇ᴸ    g) f = ◇ᴸ    (compose g f)
  compose (◇ᴿ    g) f = ◇ᴿ    (compose g f)
  compose (□ᴸ    g) f = □ᴸ    (compose g f)
  compose (□ᴿ    g) f = □ᴿ    (compose g f)
  compose (r□◇   g) f = r□◇   (compose g f)
  compose (r◇□   g) f = r◇□   (compose g f)
  compose (₀ᴸ    g) f = ₀ᴸ    (compose g f)
  compose (₀ᴿ    g) f = ₀ᴿ    (compose g f)
  compose (⁰ᴸ    g) f = ⁰ᴸ    (compose g f)
  compose (⁰ᴿ    g) f = ⁰ᴿ    (compose g f)
  compose (₁ᴸ    g) f = ₁ᴸ    (compose g f)
  compose (₁ᴿ    g) f = ₁ᴿ    (compose g f)
  compose (¹ᴸ    g) f = ¹ᴸ    (compose g f)
  compose (¹ᴿ    g) f = ¹ᴿ    (compose g f)
  compose (r⁰₀   g) f = r⁰₀   (compose g f)
  compose (r₀⁰   g) f = r₀⁰   (compose g f)
  compose (r¹₁   g) f = r¹₁   (compose g f)
  compose (r₁¹   g) f = r₁¹   (compose g f)
  compose (⊗ᴿ₁ g h) f = ⊗ᴿ₁   (compose g f) h
  compose (⊗ᴿ₂ g h) f = ⊗ᴿ₂ g (compose h f)
  compose (⊗ᴸ    g) f = ⊗ᴸ    (compose g f)
  compose (⇒ᴿ    g) f = ⇒ᴿ    (compose g f)
  compose (⇒ᴸ₁ g h) f = ⇒ᴸ₁   (compose g f) h
  compose (⇒ᴸ₂ g h) f = ⇒ᴸ₂ g (compose h f)
  compose (⇐ᴿ    g) f = ⇐ᴿ    (compose g f)
  compose (⇐ᴸ₁ g h) f = ⇐ᴸ₁   (compose g f) h
  compose (⇐ᴸ₂ g h) f = ⇐ᴸ₂ g (compose h f)
  compose (r⇒⊗   g) f = r⇒⊗   (compose g f)
  compose (r⊗⇒   g) f = r⊗⇒   (compose g f)
  compose (r⇐⊗   g) f = r⇐⊗   (compose g f)
  compose (r⊗⇐   g) f = r⊗⇐   (compose g f)
  compose (⊕ᴸ₁ g h) f = ⊕ᴸ₁   (compose g f) h
  compose (⊕ᴸ₂ g h) f = ⊕ᴸ₂ g (compose h f)
  compose (⊕ᴿ    g) f = ⊕ᴿ    (compose g f)
  compose (⇚ᴸ    g) f = ⇚ᴸ    (compose g f)
  compose (⇚ᴿ₁ g h) f = ⇚ᴿ₁   (compose g f) h
  compose (⇚ᴿ₂ g h) f = ⇚ᴿ₂ g (compose h f)
  compose (⇛ᴸ    g) f = ⇛ᴸ    (compose g f)
  compose (⇛ᴿ₁ g h) f = ⇛ᴿ₁   (compose g f) h
  compose (⇛ᴿ₂ g h) f = ⇛ᴿ₂ g (compose h f)
  compose (r⇚⊕   g) f = r⇚⊕   (compose g f)
  compose (r⊕⇚   g) f = r⊕⇚   (compose g f)
  compose (r⇛⊕   g) f = r⇛⊕   (compose g f)
  compose (r⊕⇛   g) f = r⊕⇛   (compose g f)
  compose (d⇛⇐   g) f = d⇛⇐   (compose g f)
  compose (d⇛⇒   g) f = d⇛⇒   (compose g f)
  compose (d⇚⇒   g) f = d⇚⇒   (compose g f)
  compose (d⇚⇐   g) f = d⇚⇐   (compose g f)


  def : ∀ {I J K} (f : LG I ⋯ J) (g : LG J ⋯ K) (x : LG I)
      → apply (compose g f) x ≡ apply g (apply f x)
  def f [] x = refl
  def f (⇁ g    ) x rewrite def f g x = refl
  def f (↽ g    ) x rewrite def f g x = refl
  def f (⇀ g    ) x rewrite def f g x = refl
  def f (↼ g    ) x rewrite def f g x = refl
  def f (◇ᴸ g   ) x rewrite def f g x = refl
  def f (◇ᴿ g   ) x rewrite def f g x = refl
  def f (□ᴸ g   ) x rewrite def f g x = refl
  def f (□ᴿ g   ) x rewrite def f g x = refl
  def f (r□◇ g  ) x rewrite def f g x = refl
  def f (r◇□ g  ) x rewrite def f g x = refl
  def f (₀ᴸ g   ) x rewrite def f g x = refl
  def f (₀ᴿ g   ) x rewrite def f g x = refl
  def f (⁰ᴸ g   ) x rewrite def f g x = refl
  def f (⁰ᴿ g   ) x rewrite def f g x = refl
  def f (₁ᴸ g   ) x rewrite def f g x = refl
  def f (₁ᴿ g   ) x rewrite def f g x = refl
  def f (¹ᴸ g   ) x rewrite def f g x = refl
  def f (¹ᴿ g   ) x rewrite def f g x = refl
  def f (r⁰₀ g  ) x rewrite def f g x = refl
  def f (r₀⁰ g  ) x rewrite def f g x = refl
  def f (r¹₁ g  ) x rewrite def f g x = refl
  def f (r₁¹ g  ) x rewrite def f g x = refl
  def f (⊗ᴿ₁ g _) x rewrite def f g x = refl
  def f (⊗ᴿ₂ _ g) x rewrite def f g x = refl
  def f (⊗ᴸ g   ) x rewrite def f g x = refl
  def f (⇒ᴿ g   ) x rewrite def f g x = refl
  def f (⇒ᴸ₁ g _) x rewrite def f g x = refl
  def f (⇒ᴸ₂ _ g) x rewrite def f g x = refl
  def f (⇐ᴿ g   ) x rewrite def f g x = refl
  def f (⇐ᴸ₁ g _) x rewrite def f g x = refl
  def f (⇐ᴸ₂ _ g) x rewrite def f g x = refl
  def f (r⇒⊗ g  ) x rewrite def f g x = refl
  def f (r⊗⇒ g  ) x rewrite def f g x = refl
  def f (r⇐⊗ g  ) x rewrite def f g x = refl
  def f (r⊗⇐ g  ) x rewrite def f g x = refl
  def f (⊕ᴸ₁ g _) x rewrite def f g x = refl
  def f (⊕ᴸ₂ _ g) x rewrite def f g x = refl
  def f (⊕ᴿ g   ) x rewrite def f g x = refl
  def f (⇚ᴸ g   ) x rewrite def f g x = refl
  def f (⇚ᴿ₁ g _) x rewrite def f g x = refl
  def f (⇚ᴿ₂ _ g) x rewrite def f g x = refl
  def f (⇛ᴸ g   ) x rewrite def f g x = refl
  def f (⇛ᴿ₁ g _) x rewrite def f g x = refl
  def f (⇛ᴿ₂ _ g) x rewrite def f g x = refl
  def f (r⇚⊕ g  ) x rewrite def f g x = refl
  def f (r⊕⇚ g  ) x rewrite def f g x = refl
  def f (r⇛⊕ g  ) x rewrite def f g x = refl
  def f (r⊕⇛ g  ) x rewrite def f g x = refl
  def f (d⇛⇐ g  ) x rewrite def f g x = refl
  def f (d⇛⇒ g  ) x rewrite def f g x = refl
  def f (d⇚⇒ g  ) x rewrite def f g x = refl
  def f (d⇚⇐ g  ) x rewrite def f g x = refl

  assoc : ∀ {A B C D} (f : LG A ⋯ B) (g : LG B ⋯ C) (h : LG C ⋯ D)
        → compose (compose h g) f ≡ compose h (compose g f)
  assoc f g [] = refl
  assoc f g (⇁   h  ) rewrite assoc f g h = refl
  assoc f g (↽   h  ) rewrite assoc f g h = refl
  assoc f g (⇀   h  ) rewrite assoc f g h = refl
  assoc f g (↼   h  ) rewrite assoc f g h = refl
  assoc f g (◇ᴸ  h  ) rewrite assoc f g h = refl
  assoc f g (◇ᴿ  h  ) rewrite assoc f g h = refl
  assoc f g (□ᴸ  h  ) rewrite assoc f g h = refl
  assoc f g (□ᴿ  h  ) rewrite assoc f g h = refl
  assoc f g (r□◇ h  ) rewrite assoc f g h = refl
  assoc f g (r◇□ h  ) rewrite assoc f g h = refl
  assoc f g (₀ᴸ  h  ) rewrite assoc f g h = refl
  assoc f g (₀ᴿ  h  ) rewrite assoc f g h = refl
  assoc f g (⁰ᴸ  h  ) rewrite assoc f g h = refl
  assoc f g (⁰ᴿ  h  ) rewrite assoc f g h = refl
  assoc f g (₁ᴸ  h  ) rewrite assoc f g h = refl
  assoc f g (₁ᴿ  h  ) rewrite assoc f g h = refl
  assoc f g (¹ᴸ  h  ) rewrite assoc f g h = refl
  assoc f g (¹ᴿ  h  ) rewrite assoc f g h = refl
  assoc f g (r⁰₀ h  ) rewrite assoc f g h = refl
  assoc f g (r₀⁰ h  ) rewrite assoc f g h = refl
  assoc f g (r¹₁ h  ) rewrite assoc f g h = refl
  assoc f g (r₁¹ h  ) rewrite assoc f g h = refl
  assoc f g (⊗ᴿ₁ h _) rewrite assoc f g h = refl
  assoc f g (⊗ᴿ₂ _ h) rewrite assoc f g h = refl
  assoc f g (⊗ᴸ  h  ) rewrite assoc f g h = refl
  assoc f g (⇒ᴿ  h  ) rewrite assoc f g h = refl
  assoc f g (⇒ᴸ₁ h _) rewrite assoc f g h = refl
  assoc f g (⇒ᴸ₂ _ h) rewrite assoc f g h = refl
  assoc f g (⇐ᴿ  h  ) rewrite assoc f g h = refl
  assoc f g (⇐ᴸ₁ h _) rewrite assoc f g h = refl
  assoc f g (⇐ᴸ₂ _ h) rewrite assoc f g h = refl
  assoc f g (r⇒⊗ h  ) rewrite assoc f g h = refl
  assoc f g (r⊗⇒ h  ) rewrite assoc f g h = refl
  assoc f g (r⇐⊗ h  ) rewrite assoc f g h = refl
  assoc f g (r⊗⇐ h  ) rewrite assoc f g h = refl
  assoc f g (⊕ᴸ₁ h _) rewrite assoc f g h = refl
  assoc f g (⊕ᴸ₂ _ h) rewrite assoc f g h = refl
  assoc f g (⊕ᴿ  h  ) rewrite assoc f g h = refl
  assoc f g (⇚ᴸ  h  ) rewrite assoc f g h = refl
  assoc f g (⇚ᴿ₁ h _) rewrite assoc f g h = refl
  assoc f g (⇚ᴿ₂ _ h) rewrite assoc f g h = refl
  assoc f g (⇛ᴸ  h  ) rewrite assoc f g h = refl
  assoc f g (⇛ᴿ₁ h _) rewrite assoc f g h = refl
  assoc f g (⇛ᴿ₂ _ h) rewrite assoc f g h = refl
  assoc f g (r⇚⊕ h  ) rewrite assoc f g h = refl
  assoc f g (r⊕⇚ h  ) rewrite assoc f g h = refl
  assoc f g (r⇛⊕ h  ) rewrite assoc f g h = refl
  assoc f g (r⊕⇛ h  ) rewrite assoc f g h = refl
  assoc f g (d⇛⇐ h  ) rewrite assoc f g h = refl
  assoc f g (d⇛⇒ h  ) rewrite assoc f g h = refl
  assoc f g (d⇚⇒ h  ) rewrite assoc f g h = refl
  assoc f g (d⇚⇐ h  ) rewrite assoc f g h = refl

  identity : ∀ {A B} (f : LG A ⋯ B) → compose f [] ≡ f
  identity [] = refl
  identity (⇁   f  ) rewrite identity f = refl
  identity (↽   f  ) rewrite identity f = refl
  identity (⇀   f  ) rewrite identity f = refl
  identity (↼   f  ) rewrite identity f = refl
  identity (◇ᴸ  f  ) rewrite identity f = refl
  identity (◇ᴿ  f  ) rewrite identity f = refl
  identity (□ᴸ  f  ) rewrite identity f = refl
  identity (□ᴿ  f  ) rewrite identity f = refl
  identity (r□◇ f  ) rewrite identity f = refl
  identity (r◇□ f  ) rewrite identity f = refl
  identity (₀ᴸ  f  ) rewrite identity f = refl
  identity (₀ᴿ  f  ) rewrite identity f = refl
  identity (⁰ᴸ  f  ) rewrite identity f = refl
  identity (⁰ᴿ  f  ) rewrite identity f = refl
  identity (₁ᴸ  f  ) rewrite identity f = refl
  identity (₁ᴿ  f  ) rewrite identity f = refl
  identity (¹ᴸ  f  ) rewrite identity f = refl
  identity (¹ᴿ  f  ) rewrite identity f = refl
  identity (r⁰₀ f  ) rewrite identity f = refl
  identity (r₀⁰ f  ) rewrite identity f = refl
  identity (r¹₁ f  ) rewrite identity f = refl
  identity (r₁¹ f  ) rewrite identity f = refl
  identity (⊗ᴿ₁ f _) rewrite identity f = refl
  identity (⊗ᴿ₂ _ f) rewrite identity f = refl
  identity (⊗ᴸ  f  ) rewrite identity f = refl
  identity (⇒ᴿ  f  ) rewrite identity f = refl
  identity (⇒ᴸ₁ f _) rewrite identity f = refl
  identity (⇒ᴸ₂ _ f) rewrite identity f = refl
  identity (⇐ᴿ  f  ) rewrite identity f = refl
  identity (⇐ᴸ₁ f _) rewrite identity f = refl
  identity (⇐ᴸ₂ _ f) rewrite identity f = refl
  identity (r⇒⊗ f  ) rewrite identity f = refl
  identity (r⊗⇒ f  ) rewrite identity f = refl
  identity (r⇐⊗ f  ) rewrite identity f = refl
  identity (r⊗⇐ f  ) rewrite identity f = refl
  identity (⊕ᴸ₁ f _) rewrite identity f = refl
  identity (⊕ᴸ₂ _ f) rewrite identity f = refl
  identity (⊕ᴿ  f  ) rewrite identity f = refl
  identity (⇚ᴸ  f  ) rewrite identity f = refl
  identity (⇚ᴿ₁ f _) rewrite identity f = refl
  identity (⇚ᴿ₂ _ f) rewrite identity f = refl
  identity (⇛ᴸ  f  ) rewrite identity f = refl
  identity (⇛ᴿ₁ f _) rewrite identity f = refl
  identity (⇛ᴿ₂ _ f) rewrite identity f = refl
  identity (r⇚⊕ f  ) rewrite identity f = refl
  identity (r⊕⇚ f  ) rewrite identity f = refl
  identity (r⇛⊕ f  ) rewrite identity f = refl
  identity (r⊕⇛ f  ) rewrite identity f = refl
  identity (d⇛⇐ f  ) rewrite identity f = refl
  identity (d⇛⇒ f  ) rewrite identity f = refl
  identity (d⇚⇒ f  ) rewrite identity f = refl
  identity (d⇚⇐ f  ) rewrite identity f = refl

  respect : ∀ {A B C} {f₁ f₂ : LG A ⋯ B} {g₁ g₂ : LG B ⋯ C}
          → g₁ ≡ g₂ → f₁ ≡ f₂ → compose g₁ f₁ ≡ compose g₂ f₂
  respect p₁ p₂ rewrite p₁ | p₂ = refl


instance
  category : Category ℓ ℓ ℓ
  category = record
    { Obj       = Judgement
    ; _⇒_       = LG_⋯_
    ; _≡_       = _≡_
    ; id        = []
    ; _∘_       = compose
    ; assoc     = λ {_}{_}{_}{_}{f}{g}{h} → assoc f g h
    ; identityˡ = λ {_}{_}{f} → refl
    ; identityʳ = λ {_}{_}{f} → identity f
    ; ∘-resp-≡  = respect
    ; equiv     = P.isEquivalence
    }
    where open Simple


instance
  functor : Functor category (Sets ℓ)
  functor = record
    { F₀           = LG_
    ; F₁           = apply
    ; identity     = refl
    ; homomorphism = λ {_}{_}{_}{f}{g}{x} → def f g x
    ; F-resp-≡     = respect₂
    }
    where
      open Simple
      respect₂ : ∀ {I J} {f g : LG I ⋯ J} → f ≡ g → ∀ {x} → apply f x ≡ apply g x
      respect₂ refl = refl
