------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements a proof of equivalence with the residuation-monotonicity
-- calculus as `eq`.
------------------------------------------------------------------------


open import Function.Equivalence                       using (_⇔_; equivalence)
open import Data.Product                               using (_×_; _,_; proj₂)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable                 using (fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module Logic.Classical.Ordered.LambekGrishin.EquivalentToResMon {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.Classical.Ordered.LambekGrishin.Type                Univ as LG
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Univ
open import Logic.Classical.Ordered.LambekGrishin.Judgement           Univ as LGJ
open import Logic.Classical.Ordered.LambekGrishin.Base                Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement    Univ as RMJ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base         Univ renaming (LG_ to RM_)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Origin       Univ


mutual
  -- Inflate a `Type` into a maximal positive `Structure`
  ⟦_⟧⁺ : Type → Structure +
  ⟦ ◇ A   ⟧⁺ = ⟨ ⟦ A ⟧⁺ ⟩
  ⟦ ₁ A   ⟧⁺ = ₁ ⟦ A ⟧⁻
  ⟦ A ¹   ⟧⁺ = ⟦ A ⟧⁻ ¹
  ⟦ A ⇚ B ⟧⁺ = ⟦ A ⟧⁺ ⇚ ⟦ B ⟧⁻
  ⟦ A ⇛ B ⟧⁺ = ⟦ A ⟧⁻ ⇛ ⟦ B ⟧⁺
  ⟦ A ⊗ B ⟧⁺ = ⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁺
  ⟦   A   ⟧⁺ = · A ·

  -- Inflate a `Type` into a maximal negative `Structure`
  ⟦_⟧⁻ : Type → Structure -
  ⟦ □ A   ⟧⁻ = [ ⟦ A ⟧⁻ ]
  ⟦ ₀ A   ⟧⁻ = ₀ ⟦ A ⟧⁺
  ⟦ A ⁰   ⟧⁻ = ⟦ A ⟧⁺ ⁰
  ⟦ A ⇒ B ⟧⁻ = ⟦ A ⟧⁺ ⇒ ⟦ B ⟧⁻
  ⟦ A ⇐ B ⟧⁻ = ⟦ A ⟧⁻ ⇐ ⟦ B ⟧⁺
  ⟦ A ⊕ B ⟧⁻ = ⟦ A ⟧⁻ ⊕ ⟦ B ⟧⁻
  ⟦   A   ⟧⁻ = · A ·


-- Deflate a `Structure` into a `Type`
⟦_⟧ : ∀ {p} → Structure p → Type
⟦ · A · ⟧ = A
⟦ [ X ] ⟧ = □ ⟦ X ⟧
⟦ ⟨ X ⟩ ⟧ = ◇ ⟦ X ⟧
⟦  ₀ X  ⟧ = ₀ ⟦ X ⟧
⟦  X ⁰  ⟧ = ⟦ X ⟧ ⁰
⟦  ₁ X  ⟧ = ₁ ⟦ X ⟧
⟦  X ¹  ⟧ = ⟦ X ⟧ ¹
⟦ X ⊗ Y ⟧ = ⟦ X ⟧ ⊗ ⟦ Y ⟧
⟦ X ⇚ Y ⟧ = ⟦ X ⟧ ⇚ ⟦ Y ⟧
⟦ X ⇛ Y ⟧ = ⟦ X ⟧ ⇛ ⟦ Y ⟧
⟦ X ⊕ Y ⟧ = ⟦ X ⟧ ⊕ ⟦ Y ⟧
⟦ X ⇒ Y ⟧ = ⟦ X ⟧ ⇒ ⟦ Y ⟧
⟦ X ⇐ Y ⟧ = ⟦ X ⟧ ⇐ ⟦ Y ⟧


mutual
  deflate⁺ : ∀ {A Y} → LG ⟦ A ⟧⁺ ⊢ Y → LG · A · ⊢ Y
  deflate⁺ {A = el  A} f = f
  deflate⁺ {A = □   A} f = f
  deflate⁺ {A = ◇   A} f = ◇ᴸ (r□◇ (deflate⁺ (r◇□ f)))
  deflate⁺ {A = ₀   A} f = f
  deflate⁺ {A = A   ⁰} f = f
  deflate⁺ {A = ₁   A} f = ₁ᴸ (r¹₁ (deflate⁻ (r₁¹ f)))
  deflate⁺ {A = A   ¹} f = ¹ᴸ (r₁¹ (deflate⁻ (r¹₁ f)))
  deflate⁺ {A = A ⇒ B} f = f
  deflate⁺ {A = A ⇐ B} f = f
  deflate⁺ {A = A ⇚ B} f = ⇚ᴸ (r⊕⇚ (deflate⁺ (r⇛⊕ (deflate⁻ (r⊕⇛ (r⇚⊕ f))))))
  deflate⁺ {A = A ⇛ B} f = ⇛ᴸ (r⊕⇛ (deflate⁺ (r⇚⊕ (deflate⁻ (r⊕⇚ (r⇛⊕ f))))))
  deflate⁺ {A = A ⊗ B} f = ⊗ᴸ (r⇐⊗ (deflate⁺ (r⊗⇐ (r⇒⊗ (deflate⁺ (r⊗⇒ f))))))
  deflate⁺ {A = A ⊕ B} f = f

  deflate⁻ : ∀ {X B} → LG X ⊢ ⟦ B ⟧⁻ → LG X ⊢ · B ·
  deflate⁻ {B = el  B} f = f
  deflate⁻ {B = □   B} f = □ᴿ (r◇□ (deflate⁻ (r□◇ f)))
  deflate⁻ {B = ◇   B} f = f
  deflate⁻ {B = ₀   B} f = ₀ᴿ (r⁰₀ (deflate⁺ (r₀⁰ f)))
  deflate⁻ {B = B   ⁰} f = ⁰ᴿ (r₀⁰ (deflate⁺ (r⁰₀ f)))
  deflate⁻ {B = ₁   B} f = f
  deflate⁻ {B = B   ¹} f = f
  deflate⁻ {B = B ⇒ C} f = ⇒ᴿ (r⊗⇒ (deflate⁻ (r⇐⊗ (deflate⁺ (r⊗⇐ (r⇒⊗ f))))))
  deflate⁻ {B = B ⇐ C} f = ⇐ᴿ (r⊗⇐ (deflate⁻ (r⇒⊗ (deflate⁺ (r⊗⇒ (r⇐⊗ f))))))
  deflate⁻ {B = B ⇚ C} f = f
  deflate⁻ {B = B ⇛ C} f = f
  deflate⁻ {B = B ⊗ C} f = f
  deflate⁻ {B = B ⊕ C} f = ⊕ᴿ (r⇚⊕ (deflate⁻ (r⊕⇚ (r⇛⊕ (deflate⁻ (r⊕⇛ f))))))


mutual
  reinflate⁺ : ∀ {X Y} → LG ⟦ ⟦ X ⟧ ⟧⁺ ⊢ Y → LG X ⊢ Y
  reinflate⁺ {X = · A ·} f = deflate⁺ f
  reinflate⁺ {X = ⟨ X ⟩} f = r□◇ (reinflate⁺ (r◇□ f))
  reinflate⁺ {X = ₁   X} f = r¹₁ (reinflate⁻ (r₁¹ f))
  reinflate⁺ {X = X   ¹} f = r₁¹ (reinflate⁻ (r¹₁ f))
  reinflate⁺ {X = X ⊗ Y} f = r⇐⊗ (reinflate⁺ (r⊗⇐ (r⇒⊗ (reinflate⁺ (r⊗⇒ f)))))
  reinflate⁺ {X = X ⇚ Y} f = r⊕⇚ (reinflate⁺ (r⇛⊕ (reinflate⁻ (r⊕⇛ (r⇚⊕ f)))))
  reinflate⁺ {X = X ⇛ Y} f = r⊕⇛ (reinflate⁺ (r⇚⊕ (reinflate⁻ (r⊕⇚ (r⇛⊕ f)))))

  reinflate⁻ : ∀ {X Y} → LG X ⊢ ⟦ ⟦ Y ⟧ ⟧⁻ → LG X ⊢ Y
  reinflate⁻ {Y = · A ·} f = deflate⁻ f
  reinflate⁻ {Y = [ Y ]} f = r◇□ (reinflate⁻ (r□◇ f))
  reinflate⁻ {Y = ₀   Y} f = r⁰₀ (reinflate⁺ (r₀⁰ f))
  reinflate⁻ {Y = Y   ⁰} f = r₀⁰ (reinflate⁺ (r⁰₀ f))
  reinflate⁻ {Y = X ⊕ Y} f = r⇛⊕ (reinflate⁻ (r⊕⇛ (r⇚⊕ (reinflate⁻ (r⊕⇚ f)))))
  reinflate⁻ {Y = X ⇒ Y} f = r⊗⇒ (reinflate⁻ (r⇐⊗ (reinflate⁺ (r⊗⇐ (r⇒⊗ f)))))
  reinflate⁻ {Y = X ⇐ Y} f = r⊗⇐ (reinflate⁻ (r⇒⊗ (reinflate⁺ (r⊗⇒ (r⇐⊗ f)))))


To : LGJ.Judgement → RMJ.Judgement
To (  X  ⊢  Y  ) = ⟦ X ⟧ ⊢ ⟦ Y ⟧
To ([ A ]⊢  Y  ) =   A   ⊢ ⟦ Y ⟧
To (  X  ⊢[ B ]) = ⟦ X ⟧ ⊢   B


to : ∀ {J} → LG J → RM (To J)
to  ax⁺      = ax′
to  ax⁻      = ax′
to (⇁   f  ) = to f
to (↽   f  ) = to f
to (⇀   f  ) = to f
to (↼   f  ) = to f
to (◇ᴸ  f  ) = to f
to (◇ᴿ  f  ) = m◇  (to f)
to (□ᴸ  f  ) = m□  (to f)
to (□ᴿ  f  ) = to f
to (r□◇ f  ) = r□◇ (to f)
to (r◇□ f  ) = r◇□ (to f)
to (₀ᴸ  f  ) = m₀  (to f)
to (₀ᴿ  f  ) = to f
to (⁰ᴸ  f  ) = m⁰  (to f)
to (⁰ᴿ  f  ) = to f
to (₁ᴸ  f  ) = to f
to (₁ᴿ  f  ) = m₁  (to f)
to (¹ᴸ  f  ) = to f
to (¹ᴿ  f  ) = m¹  (to f)
to (r⁰₀ f  ) = r⁰₀ (to f)
to (r₀⁰ f  ) = r₀⁰ (to f)
to (r¹₁ f  ) = r¹₁ (to f)
to (r₁¹ f  ) = r₁¹ (to f)
to (⊗ᴸ  f  ) = to f
to (⊗ᴿ  f g) = m⊗  (to f) (to g)
to (⇒ᴸ  f g) = m⇒  (to f) (to g)
to (⇒ᴿ  f  ) = to f
to (⇐ᴸ  f g) = m⇐  (to g) (to f)
to (⇐ᴿ  f  ) = to f
to (r⇒⊗ f  ) = r⇒⊗ (to f)
to (r⊗⇒ f  ) = r⊗⇒ (to f)
to (r⇐⊗ f  ) = r⇐⊗ (to f)
to (r⊗⇐ f  ) = r⊗⇐ (to f)
to (⊕ᴸ  f g) = m⊕  (to f) (to g)
to (⊕ᴿ  f  ) = to f
to (⇚ᴸ  f  ) = to f
to (⇚ᴿ  f g) = m⇚  (to f) (to g)
to (⇛ᴸ  f  ) = to f
to (⇛ᴿ  f g) = m⇛  (to g) (to f)
to (r⇚⊕ f  ) = r⇚⊕ (to f)
to (r⊕⇚ f  ) = r⊕⇚ (to f)
to (r⇛⊕ f  ) = r⇛⊕ (to f)
to (r⊕⇛ f  ) = r⊕⇛ (to f)
to (d⇛⇐ f  ) = d⇛⇐ (to f)
to (d⇛⇒ f  ) = d⇛⇒ (to f)
to (d⇚⇒ f  ) = d⇚⇒ (to f)
to (d⇚⇐ f  ) = d⇚⇐ (to f)


From : (J : RMJ.Judgement) → LGJ.Judgement
From (A ⊢ B) = ⟦ A ⟧⁺ ⊢ ⟦ B ⟧⁻


from : ∀ {J} → RM J → LG (From J)
from (ax     ) = ⇀ ax⁺
from (m□  f  ) = ↼ (□ᴸ (↽ (deflate⁺ (from f))))
from (m◇  f  ) = ⇀ (◇ᴿ (⇁ (deflate⁻ (from f))))
from (m₀  f  ) = ↼ (₀ᴸ (⇁ (deflate⁻ (from f))))
from (m⁰  f  ) = ↼ (⁰ᴸ (⇁ (deflate⁻ (from f))))
from (m₁  f  ) = ⇀ (₁ᴿ (↽ (deflate⁺ (from f))))
from (m¹  f  ) = ⇀ (¹ᴿ (↽ (deflate⁺ (from f))))
from (m⊗  f g) = ⇀ (⊗ᴿ (⇁ (deflate⁻ (from f))) (⇁ (deflate⁻ (from g))))
from (m⇒  f g) = ↼ (⇒ᴸ (⇁ (deflate⁻ (from f))) (↽ (deflate⁺ (from g))))
from (m⇐  f g) = ↼ (⇐ᴸ (⇁ (deflate⁻ (from g))) (↽ (deflate⁺ (from f))))
from (m⊕  f g) = ↼ (⊕ᴸ (↽ (deflate⁺ (from f))) (↽ (deflate⁺ (from g))))
from (m⇛  f g) = ⇀ (⇛ᴿ (⇁ (deflate⁻ (from g))) (↽ (deflate⁺ (from f))))
from (m⇚  f g) = ⇀ (⇚ᴿ (⇁ (deflate⁻ (from f))) (↽ (deflate⁺ (from g))))
from (r□◇ f  ) = r□◇ (from f)
from (r◇□ f  ) = r◇□ (from f)
from (r⁰₀ f  ) = r⁰₀ (from f)
from (r₀⁰ f  ) = r₀⁰ (from f)
from (r¹₁ f  ) = r¹₁ (from f)
from (r₁¹ f  ) = r₁¹ (from f)
from (r⇒⊗ f  ) = r⇒⊗ (from f)
from (r⊗⇒ f  ) = r⊗⇒ (from f)
from (r⇐⊗ f  ) = r⇐⊗ (from f)
from (r⊗⇐ f  ) = r⊗⇐ (from f)
from (r⇛⊕ f  ) = r⇛⊕ (from f)
from (r⊕⇛ f  ) = r⊕⇛ (from f)
from (r⊕⇚ f  ) = r⊕⇚ (from f)
from (r⇚⊕ f  ) = r⇚⊕ (from f)
from (d⇛⇐ f  ) = d⇛⇐ (from f)
from (d⇛⇒ f  ) = d⇛⇒ (from f)
from (d⇚⇒ f  ) = d⇚⇒ (from f)
from (d⇚⇐ f  ) = d⇚⇐ (from f)


From∘To : ∀ {J} → LG (From (To J)) → LG J
From∘To {  X  ⊢  Y  } f =   (reinflate⁻ (reinflate⁺ f))
From∘To {[ A ]⊢  Y  } f = ↽ (reinflate⁻ (deflate⁺   f))
From∘To {  X  ⊢[ B ]} f = ⇁ (deflate⁻   (reinflate⁺ f))
