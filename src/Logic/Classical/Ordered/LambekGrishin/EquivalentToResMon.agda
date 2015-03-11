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

open import Logic.Classical.Ordered.LambekGrishin.Type                Univ as RM using ()
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement    Univ as RMJ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base         Univ renaming (LG_ to RM_)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Origin       Univ


module To where

  ⟦_⟧ : LG.Type → RM.Type
  ⟦ el A  ⟧ = RM.el A
  ⟦  □ A  ⟧ = RM.□ ⟦ A ⟧
  ⟦  ◇ A  ⟧ = RM.◇ ⟦ A ⟧
  ⟦  ₀ A  ⟧ = RM.₀ ⟦ A ⟧
  ⟦  A ⁰  ⟧ = ⟦ A ⟧ RM.⁰
  ⟦  ₁ A  ⟧ = RM.₁ ⟦ A ⟧
  ⟦  A ¹  ⟧ = ⟦ A ⟧ RM.¹
  ⟦ A ⇒ B ⟧ = ⟦ A ⟧ RM.⇒ ⟦ B ⟧
  ⟦ A ⇐ B ⟧ = ⟦ A ⟧ RM.⇐ ⟦ B ⟧
  ⟦ A ⇚ B ⟧ = ⟦ A ⟧ RM.⇚ ⟦ B ⟧
  ⟦ A ⇛ B ⟧ = ⟦ A ⟧ RM.⇛ ⟦ B ⟧
  ⟦ A ⊗ B ⟧ = ⟦ A ⟧ RM.⊗ ⟦ B ⟧
  ⟦ A ⊕ B ⟧ = ⟦ A ⟧ RM.⊕ ⟦ B ⟧


  ⟦_⟧ˢ : ∀ {p} → Structure p → RM.Type
  ⟦ · A · ⟧ˢ = ⟦ A ⟧
  ⟦ [ X ] ⟧ˢ = RM.□ ⟦ X ⟧ˢ
  ⟦ ⟨ X ⟩ ⟧ˢ = RM.◇ ⟦ X ⟧ˢ
  ⟦  ₀ X  ⟧ˢ = RM.₀ ⟦ X ⟧ˢ
  ⟦  X ⁰  ⟧ˢ = ⟦ X ⟧ˢ RM.⁰
  ⟦  ₁ X  ⟧ˢ = RM.₁ ⟦ X ⟧ˢ
  ⟦  X ¹  ⟧ˢ = ⟦ X ⟧ˢ RM.¹
  ⟦ X ⊗ Y ⟧ˢ = ⟦ X ⟧ˢ RM.⊗ ⟦ Y ⟧ˢ
  ⟦ X ⇚ Y ⟧ˢ = ⟦ X ⟧ˢ RM.⇚ ⟦ Y ⟧ˢ
  ⟦ X ⇛ Y ⟧ˢ = ⟦ X ⟧ˢ RM.⇛ ⟦ Y ⟧ˢ
  ⟦ X ⊕ Y ⟧ˢ = ⟦ X ⟧ˢ RM.⊕ ⟦ Y ⟧ˢ
  ⟦ X ⇒ Y ⟧ˢ = ⟦ X ⟧ˢ RM.⇒ ⟦ Y ⟧ˢ
  ⟦ X ⇐ Y ⟧ˢ = ⟦ X ⟧ˢ RM.⇐ ⟦ Y ⟧ˢ


  To : LGJ.Judgement → RMJ.Judgement
  To (  X  ⊢  Y  ) = ⟦ X ⟧ˢ ⊢ ⟦ Y ⟧ˢ
  To ([ A ]⊢  Y  ) = ⟦ A ⟧ ⊢ ⟦ Y ⟧ˢ
  To (  X  ⊢[ B ]) = ⟦ X ⟧ˢ ⊢ ⟦ B ⟧


  to : ∀ {J} → LG J → RM (To J)
  to (ax⁺    ) = ax′
  to (ax⁻    ) = ax′
  to (⇁   f  ) = to f
  to (↽   f  ) = to f
  to (⇀   f  ) = to f
  to (↼   f  ) = to f
  to (◇ᴸ  f  ) = to f
  to (◇ᴿ  f  ) = m◇ (to f)
  to (□ᴸ  f  ) = m□ (to f)
  to (□ᴿ  f  ) = to f
  to (₀ᴸ  f  ) = m₀ (to f)
  to (₀ᴿ  f  ) = to f
  to (⁰ᴸ  f  ) = m⁰ (to f)
  to (⁰ᴿ  f  ) = to f
  to (₁ᴸ  f  ) = to f
  to (₁ᴿ  f  ) = m₁ (to f)
  to (¹ᴸ  f  ) = to f
  to (¹ᴿ  f  ) = m¹ (to f)
  to (⊗ᴿ  f g) = m⊗ (to f) (to g)
  to (⇚ᴿ  f g) = m⇚ (to f) (to g)
  to (⇛ᴿ  f g) = m⇛ (to g) (to f)
  to (⊕ᴸ  f g) = m⊕ (to f) (to g)
  to (⇒ᴸ  f g) = m⇒ (to f) (to g)
  to (⇐ᴸ  f g) = m⇐ (to g) (to f)
  to (⊗ᴸ  f  ) = to f
  to (⇚ᴸ  f  ) = to f
  to (⇛ᴸ  f  ) = to f
  to (⊕ᴿ  f  ) = to f
  to (⇒ᴿ  f  ) = to f
  to (⇐ᴿ  f  ) = to f
  to (r□◇ f  ) = r□◇ (to f)
  to (r◇□ f  ) = r◇□ (to f)
  to (r⁰₀ f  ) = r⁰₀ (to f)
  to (r₀⁰ f  ) = r₀⁰ (to f)
  to (r¹₁ f  ) = r¹₁ (to f)
  to (r₁¹ f  ) = r₁¹ (to f)
  to (r⇒⊗ f  ) = r⇒⊗ (to f)
  to (r⊗⇒ f  ) = r⊗⇒ (to f)
  to (r⇐⊗ f  ) = r⇐⊗ (to f)
  to (r⊗⇐ f  ) = r⊗⇐ (to f)
  to (r⇚⊕ f  ) = r⇚⊕ (to f)
  to (r⊕⇚ f  ) = r⊕⇚ (to f)
  to (r⇛⊕ f  ) = r⇛⊕ (to f)
  to (r⊕⇛ f  ) = r⊕⇛ (to f)
  to (d⇛⇐ f  ) = d⇛⇐ (to f)
  to (d⇛⇒ f  ) = d⇛⇒ (to f)
  to (d⇚⇒ f  ) = d⇚⇒ (to f)
  to (d⇚⇐ f  ) = d⇚⇐ (to f)



module From where

  ⟦_⟧ : RM.Type → LG.Type
  ⟦ RM.el A  ⟧ = el  A
  ⟦ RM.□ A   ⟧ = □ ⟦ A ⟧
  ⟦ RM.◇ A   ⟧ = ◇ ⟦ A ⟧
  ⟦ RM.₀ A   ⟧ = ₀ ⟦ A ⟧
  ⟦ A RM.⁰   ⟧ = ⟦ A ⟧ ⁰
  ⟦ RM.₁ A   ⟧ = ₁ ⟦ A ⟧
  ⟦ A RM.¹   ⟧ = ⟦ A ⟧ ¹
  ⟦ A RM.⇒ B ⟧ = ⟦ A ⟧ ⇒ ⟦ B ⟧
  ⟦ A RM.⇐ B ⟧ = ⟦ A ⟧ ⇐ ⟦ B ⟧
  ⟦ A RM.⇚ B ⟧ = ⟦ A ⟧ ⇚ ⟦ B ⟧
  ⟦ A RM.⇛ B ⟧ = ⟦ A ⟧ ⇛ ⟦ B ⟧
  ⟦ A RM.⊗ B ⟧ = ⟦ A ⟧ ⊗ ⟦ B ⟧
  ⟦ A RM.⊕ B ⟧ = ⟦ A ⟧ ⊕ ⟦ B ⟧


  mutual
    ⟦_⟧⁺ : RM.Type → Structure +
    ⟦ ◇ A   ⟧⁺ = ⟨ ⟦ A ⟧⁺ ⟩
    ⟦ ₁ A   ⟧⁺ = ₁ ⟦ A ⟧⁻
    ⟦ A ¹   ⟧⁺ = ⟦ A ⟧⁻ ¹
    ⟦ A ⇚ B ⟧⁺ = ⟦ A ⟧⁺ ⇚ ⟦ B ⟧⁻
    ⟦ A ⇛ B ⟧⁺ = ⟦ A ⟧⁻ ⇛ ⟦ B ⟧⁺
    ⟦ A ⊗ B ⟧⁺ = ⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁺
    ⟦   A   ⟧⁺ = · ⟦ A ⟧ ·

    ⟦_⟧⁻ : RM.Type → Structure -
    ⟦ □ A   ⟧⁻ = [ ⟦ A ⟧⁻ ]
    ⟦ ₀ A   ⟧⁻ = ₀ ⟦ A ⟧⁺
    ⟦ A ⁰   ⟧⁻ = ⟦ A ⟧⁺ ⁰
    ⟦ A ⇒ B ⟧⁻ = ⟦ A ⟧⁺ ⇒ ⟦ B ⟧⁻
    ⟦ A ⇐ B ⟧⁻ = ⟦ A ⟧⁻ ⇐ ⟦ B ⟧⁺
    ⟦ A ⊕ B ⟧⁻ = ⟦ A ⟧⁻ ⊕ ⟦ B ⟧⁻
    ⟦   A   ⟧⁻ = · ⟦ A ⟧ ·

  mutual
    lem-⟦·⟧⁺ : ∀ {A Y} → LG ⟦ A ⟧⁺ ⊢ Y → LG · ⟦ A ⟧ · ⊢ Y
    lem-⟦·⟧⁺ {A = el A}  f = f
    lem-⟦·⟧⁺ {A = □ A}   f = f
    lem-⟦·⟧⁺ {A = ◇ A}   f = ◇ᴸ (r□◇ (lem-⟦·⟧⁺ (r◇□ f)))
    lem-⟦·⟧⁺ {A = ₀ A}   f = f
    lem-⟦·⟧⁺ {A = A ⁰}   f = f
    lem-⟦·⟧⁺ {A = ₁ A}   f = ₁ᴸ (r¹₁ (lem-⟦·⟧⁻ (r₁¹ f)))
    lem-⟦·⟧⁺ {A = A ¹}   f = ¹ᴸ (r₁¹ (lem-⟦·⟧⁻ (r¹₁ f)))
    lem-⟦·⟧⁺ {A = A ⇒ B} f = f
    lem-⟦·⟧⁺ {A = A ⇐ B} f = f
    lem-⟦·⟧⁺ {A = A ⇚ B} f = ⇚ᴸ (r⊕⇚ (lem-⟦·⟧⁺ (r⇛⊕ (lem-⟦·⟧⁻ (r⊕⇛ (r⇚⊕ f))))))
    lem-⟦·⟧⁺ {A = A ⇛ B} f = ⇛ᴸ (r⊕⇛ (lem-⟦·⟧⁺ (r⇚⊕ (lem-⟦·⟧⁻ (r⊕⇚ (r⇛⊕ f))))))
    lem-⟦·⟧⁺ {A = A ⊗ B} f = ⊗ᴸ (r⇐⊗ (lem-⟦·⟧⁺ (r⊗⇐ (r⇒⊗ (lem-⟦·⟧⁺ (r⊗⇒ f))))))
    lem-⟦·⟧⁺ {A = A ⊕ B} f = f

    lem-⟦·⟧⁻ : ∀ {X B} → LG X ⊢ ⟦ B ⟧⁻ → LG X ⊢ · ⟦ B ⟧ ·
    lem-⟦·⟧⁻ {B = el B}  f = f
    lem-⟦·⟧⁻ {B = □ B}   f = □ᴿ (r◇□ (lem-⟦·⟧⁻ (r□◇ f)))
    lem-⟦·⟧⁻ {B = ◇ B}   f = f
    lem-⟦·⟧⁻ {B = ₀ B}   f = ₀ᴿ (r⁰₀ (lem-⟦·⟧⁺ (r₀⁰ f)))
    lem-⟦·⟧⁻ {B = B ⁰}   f = ⁰ᴿ (r₀⁰ (lem-⟦·⟧⁺ (r⁰₀ f)))
    lem-⟦·⟧⁻ {B = ₁ B}   f = f
    lem-⟦·⟧⁻ {B = B ¹}   f = f
    lem-⟦·⟧⁻ {B = B ⇒ C} f = ⇒ᴿ (r⊗⇒ (lem-⟦·⟧⁻ (r⇐⊗ (lem-⟦·⟧⁺ (r⊗⇐ (r⇒⊗ f))))))
    lem-⟦·⟧⁻ {B = B ⇐ C} f = ⇐ᴿ (r⊗⇐ (lem-⟦·⟧⁻ (r⇒⊗ (lem-⟦·⟧⁺ (r⊗⇒ (r⇐⊗ f))))))
    lem-⟦·⟧⁻ {B = B ⇚ C} f = f
    lem-⟦·⟧⁻ {B = B ⇛ C} f = f
    lem-⟦·⟧⁻ {B = B ⊗ C} f = f
    lem-⟦·⟧⁻ {B = B ⊕ C} f = ⊕ᴿ (r⇚⊕ (lem-⟦·⟧⁻ (r⊕⇚ (r⇛⊕ (lem-⟦·⟧⁻ (r⊕⇛ f))))))


  From : (J : RMJ.Judgement) → LGJ.Judgement
  From (A ⊢ B) = ⟦ A ⟧⁺ ⊢ ⟦ B ⟧⁻


  from : ∀ {J} → RM J → LG (From J)
  from (ax     ) = ⇀ ax⁺
  from (m□  f  ) = ↼ (□ᴸ (↽ (lem-⟦·⟧⁺ (from f))))
  from (m◇  f  ) = ⇀ (◇ᴿ (⇁ (lem-⟦·⟧⁻ (from f))))
  from (m₀  f  ) = ↼ (₀ᴸ (⇁ (lem-⟦·⟧⁻ (from f))))
  from (m⁰  f  ) = ↼ (⁰ᴸ (⇁ (lem-⟦·⟧⁻ (from f))))
  from (m₁  f  ) = ⇀ (₁ᴿ (↽ (lem-⟦·⟧⁺ (from f))))
  from (m¹  f  ) = ⇀ (¹ᴿ (↽ (lem-⟦·⟧⁺ (from f))))
  from (m⊗  f g) = ⇀ (⊗ᴿ (⇁ (lem-⟦·⟧⁻ (from f))) (⇁ (lem-⟦·⟧⁻ (from g))))
  from (m⇒  f g) = ↼ (⇒ᴸ (⇁ (lem-⟦·⟧⁻ (from f))) (↽ (lem-⟦·⟧⁺ (from g))))
  from (m⇐  f g) = ↼ (⇐ᴸ (⇁ (lem-⟦·⟧⁻ (from g))) (↽ (lem-⟦·⟧⁺ (from f))))
  from (m⊕  f g) = ↼ (⊕ᴸ (↽ (lem-⟦·⟧⁺ (from f))) (↽ (lem-⟦·⟧⁺ (from g))))
  from (m⇛  f g) = ⇀ (⇛ᴿ (⇁ (lem-⟦·⟧⁻ (from g))) (↽ (lem-⟦·⟧⁺ (from f))))
  from (m⇚  f g) = ⇀ (⇚ᴿ (⇁ (lem-⟦·⟧⁻ (from f))) (↽ (lem-⟦·⟧⁺ (from g))))
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
