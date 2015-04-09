------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements proofs of equivalence with the residuation-monotonicity
-- calculus as `eq↑` and `eq↓`.
--
-- Every proof in `LG` maps to *exactly one* proof in `RM`, namely a
-- proof for the judgement obtained by flattening all structures (as
-- per `⟦_⟧`) and removing focus.
--
-- However, every proof in `RM` maps to a number of proofs in `LG`,
-- namely the gradient between the maximally structured judgements,
-- taking polarity into account, and the judgement with two atomic
-- structures.
--
-- This module implements the translation from `LG` to `RM` as `to`,
-- and the two extremes in the translation from `RM` to `LG` as
-- `from↑` and `from↓`. The translation `from↑` maps formulae to their
-- maximally structured forms. The translation `from↓` embeds formulae
-- to atomic structures.
--
-- As a corollary, we import the proof of transitivity from the system
-- `RM`, and derive the inverted structural rules and the logical
-- forms of the residuation rules.
------------------------------------------------------------------------


open import Function                                   using (_∘_)
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
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Trans        Univ as RM using ()


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



-- Map Judgement between systems
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



-- First version of converting from RM to LG, projecting the types in
-- RM to their maximal structures in LG.
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


deflate : ∀ {A B} → LG ⟦ A ⟧⁺ ⊢ ⟦ B ⟧⁻ → LG · A · ⊢ · B ·
deflate = deflate⁺ ∘ deflate⁻


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


reinflate : ∀ {X Y} → LG ⟦ ⟦ X ⟧ ⟧⁺ ⊢ ⟦ ⟦ Y ⟧ ⟧⁻ → LG X ⊢ Y
reinflate = reinflate⁺ ∘ reinflate⁻


from↑ : ∀ {A B} → RM A ⊢ B → LG ⟦ A ⟧⁺ ⊢ ⟦ B ⟧⁻
from↑ (ax     ) = ⇀ ax⁺
from↑ (m□  f  ) = ↼ (□ᴸ (↽ (deflate⁺ (from↑ f))))
from↑ (m◇  f  ) = ⇀ (◇ᴿ (⇁ (deflate⁻ (from↑ f))))
from↑ (m₀  f  ) = ↼ (₀ᴸ (⇁ (deflate⁻ (from↑ f))))
from↑ (m⁰  f  ) = ↼ (⁰ᴸ (⇁ (deflate⁻ (from↑ f))))
from↑ (m₁  f  ) = ⇀ (₁ᴿ (↽ (deflate⁺ (from↑ f))))
from↑ (m¹  f  ) = ⇀ (¹ᴿ (↽ (deflate⁺ (from↑ f))))
from↑ (m⊗  f g) = ⇀ (⊗ᴿ (⇁ (deflate⁻ (from↑ f))) (⇁ (deflate⁻ (from↑ g))))
from↑ (m⇒  f g) = ↼ (⇒ᴸ (⇁ (deflate⁻ (from↑ f))) (↽ (deflate⁺ (from↑ g))))
from↑ (m⇐  f g) = ↼ (⇐ᴸ (⇁ (deflate⁻ (from↑ g))) (↽ (deflate⁺ (from↑ f))))
from↑ (m⊕  f g) = ↼ (⊕ᴸ (↽ (deflate⁺ (from↑ f))) (↽ (deflate⁺ (from↑ g))))
from↑ (m⇛  f g) = ⇀ (⇛ᴿ (⇁ (deflate⁻ (from↑ g))) (↽ (deflate⁺ (from↑ f))))
from↑ (m⇚  f g) = ⇀ (⇚ᴿ (⇁ (deflate⁻ (from↑ f))) (↽ (deflate⁺ (from↑ g))))
from↑ (r□◇ f  ) = r□◇ (from↑ f)
from↑ (r◇□ f  ) = r◇□ (from↑ f)
from↑ (r⁰₀ f  ) = r⁰₀ (from↑ f)
from↑ (r₀⁰ f  ) = r₀⁰ (from↑ f)
from↑ (r¹₁ f  ) = r¹₁ (from↑ f)
from↑ (r₁¹ f  ) = r₁¹ (from↑ f)
from↑ (r⇒⊗ f  ) = r⇒⊗ (from↑ f)
from↑ (r⊗⇒ f  ) = r⊗⇒ (from↑ f)
from↑ (r⇐⊗ f  ) = r⇐⊗ (from↑ f)
from↑ (r⊗⇐ f  ) = r⊗⇐ (from↑ f)
from↑ (r⇛⊕ f  ) = r⇛⊕ (from↑ f)
from↑ (r⊕⇛ f  ) = r⊕⇛ (from↑ f)
from↑ (r⊕⇚ f  ) = r⊕⇚ (from↑ f)
from↑ (r⇚⊕ f  ) = r⇚⊕ (from↑ f)
from↑ (d⇛⇐ f  ) = d⇛⇐ (from↑ f)
from↑ (d⇛⇒ f  ) = d⇛⇒ (from↑ f)
from↑ (d⇚⇒ f  ) = d⇚⇒ (from↑ f)
from↑ (d⇚⇐ f  ) = d⇚⇐ (from↑ f)


trans′ : ∀ {X A Y} → LG X ⊢[ A ] → LG [ A ]⊢ Y → LG X ⊢ Y
trans′ f g = reinflate (from↑ (RM.trans′ (to f) (to g)))


-- Inverted versions of structural rules which reintroduce
-- structures.
◇ᴸ′ : ∀ {Y A} → LG · ◇ A · ⊢ Y → LG ⟨ · A · ⟩ ⊢ Y
◇ᴸ′ f = trans′ (◇ᴿ ax⁺) (↽ f)

□ᴿ′ : ∀ {X A} → LG X ⊢ · □ A · → LG X ⊢ [ · A · ]
□ᴿ′ f = trans′ (⇁ f) (□ᴸ ax⁻)

₀ᴿ′ : ∀ {X A} → LG X ⊢ · ₀ A · → LG X ⊢ ₀ · A ·
₀ᴿ′ f = trans′ (⇁ f) (₀ᴸ ax⁺)

⁰ᴿ′ : ∀ {X A} → LG X ⊢ · A ⁰ · → LG X ⊢ · A · ⁰
⁰ᴿ′ f = trans′ (⇁ f) (⁰ᴸ ax⁺)

₁ᴸ′ : ∀ {Y A} → LG · ₁ A · ⊢ Y → LG ₁ · A · ⊢ Y
₁ᴸ′ f = trans′ (₁ᴿ ax⁻) (↽ f)

¹ᴸ′ : ∀ {Y A} → LG · A ¹ · ⊢ Y → LG · A · ¹ ⊢ Y
¹ᴸ′ f = trans′ (¹ᴿ ax⁻) (↽ f)

⊗ᴸ′ : ∀ {Y A B} → LG · A ⊗ B · ⊢ Y → LG · A · ⊗ · B · ⊢ Y
⊗ᴸ′ f = trans′ (⊗ᴿ ax⁺ ax⁺) (↽ f)

⇒ᴿ′ : ∀ {X A B} → LG X ⊢ · A ⇒ B · → LG X ⊢ · A · ⇒ · B ·
⇒ᴿ′ f = trans′ (⇁ f) (⇒ᴸ ax⁺ ax⁻)

⇐ᴿ′ : ∀ {X A B} → LG X ⊢ · B ⇐ A · → LG X ⊢ · B · ⇐ · A ·
⇐ᴿ′ f = trans′ (⇁ f) (⇐ᴸ ax⁺ ax⁻)

⊕ᴿ′ : ∀ {X A B} → LG X ⊢ · B ⊕ A · → LG X ⊢ · B · ⊕ · A ·
⊕ᴿ′ f = trans′ (⇁ f) (⊕ᴸ ax⁻ ax⁻)

⇚ᴸ′ : ∀ {X A B} → LG · A ⇚ B · ⊢ X → LG · A · ⇚ · B · ⊢ X
⇚ᴸ′ f = trans′ (⇚ᴿ ax⁺ ax⁻) (↽ f)

⇛ᴸ′ : ∀ {X A B} → LG · B ⇛ A · ⊢ X → LG · B · ⇛ · A · ⊢ X
⇛ᴸ′ f = trans′ (⇛ᴿ ax⁺ ax⁻) (↽ f)

r□◇′ : ∀ {A B} → LG · A · ⊢ · □ B · → LG · ◇ A · ⊢ · B ·
r□◇′ f = ◇ᴸ (r□◇ (□ᴿ′ f))

r◇□′ : ∀ {A B} → LG · ◇ A · ⊢ · B · → LG · A · ⊢ · □ B ·
r◇□′ f = □ᴿ (r◇□ (◇ᴸ′ f))

r⁰₀′ : ∀ {A B} → LG · A · ⊢ · B ⁰ · → LG · B · ⊢ · ₀ A ·
r⁰₀′ f = ₀ᴿ (r⁰₀ (⁰ᴿ′ f))

r₀⁰′ : ∀ {A B} → LG · B · ⊢ · ₀ A · → LG · A · ⊢ · B ⁰ ·
r₀⁰′ f = ⁰ᴿ (r₀⁰ (₀ᴿ′ f))

r¹₁′ : ∀ {A B} → LG · A ¹ · ⊢ · B · → LG · ₁ B · ⊢ · A ·
r¹₁′ f = ₁ᴸ (r¹₁ (¹ᴸ′ f))

r₁¹′ : ∀ {A B} → LG · ₁ B · ⊢ · A · → LG · A ¹ · ⊢ · B ·
r₁¹′ f = ¹ᴸ (r₁¹ (₁ᴸ′ f))

r⇒⊗′ : ∀ {A B C} → LG · B · ⊢ · A ⇒ C · → LG · A ⊗ B · ⊢ · C ·
r⇒⊗′ f = ⊗ᴸ (r⇒⊗ (⇒ᴿ′ f))

r⊗⇒′ : ∀ {A B C} → LG · A ⊗ B · ⊢ · C · → LG · B · ⊢ · A ⇒ C ·
r⊗⇒′ f = ⇒ᴿ (r⊗⇒ (⊗ᴸ′ f))

r⇐⊗′ : ∀ {A B C} → LG · A · ⊢ · C ⇐ B · → LG · A ⊗ B · ⊢ · C ·
r⇐⊗′ f = ⊗ᴸ (r⇐⊗ (⇐ᴿ′ f))

r⊗⇐′ : ∀ {A B C} → LG · A ⊗ B · ⊢ · C · → LG · A · ⊢ · C ⇐ B ·
r⊗⇐′ f = ⇐ᴿ (r⊗⇐ (⊗ᴸ′ f))

r⇚⊕′ : ∀ {A B C} → LG · C ⇚ A · ⊢ · B · → LG · C · ⊢ · B ⊕ A ·
r⇚⊕′ f = ⊕ᴿ (r⇚⊕ (⇚ᴸ′ f))

r⊕⇚′ : ∀ {A B C} → LG · C · ⊢ · B ⊕ A · → LG · C ⇚ A · ⊢ · B ·
r⊕⇚′ f = ⇚ᴸ (r⊕⇚ (⊕ᴿ′ f))

r⇛⊕′ : ∀ {A B C} → LG · B ⇛ C · ⊢ · A · → LG · C · ⊢ · B ⊕ A ·
r⇛⊕′ f = ⊕ᴿ (r⇛⊕ (⇛ᴸ′ f))

r⊕⇛′ : ∀ {A B C} → LG · C · ⊢ · B ⊕ A · → LG · B ⇛ C · ⊢ · A ·
r⊕⇛′ f = ⇛ᴸ (r⊕⇛ (⊕ᴿ′ f))

d⇛⇐′ : ∀ {A B C D} → LG · A ⊗ B · ⊢ · C ⊕ D · → LG · C ⇛ A · ⊢ · D ⇐ B ·
d⇛⇐′ f = ⇐ᴿ (⇛ᴸ (d⇛⇐ (⊗ᴸ′ (⊕ᴿ′ f))))

d⇛⇒′ : ∀ {A B C D} → LG · A ⊗ B · ⊢ · C ⊕ D · → LG · C ⇛ B · ⊢ · A ⇒ D ·
d⇛⇒′ f = ⇒ᴿ (⇛ᴸ (d⇛⇒ (⊗ᴸ′ (⊕ᴿ′ f))))

d⇚⇒′ : ∀ {A B C D} → LG · A ⊗ B · ⊢ · C ⊕ D · → LG · B ⇚ D · ⊢ · A ⇒ C ·
d⇚⇒′ f = ⇒ᴿ (⇚ᴸ (d⇚⇒ (⊗ᴸ′ (⊕ᴿ′ f))))

d⇚⇐′ : ∀ {A B C D} → LG · A ⊗ B · ⊢ · C ⊕ D · → LG · A ⇚ D · ⊢ · C ⇐ B ·
d⇚⇐′ f = ⇐ᴿ (⇚ᴸ (d⇚⇐ (⊗ᴸ′ (⊕ᴿ′ f))))

from↓ : ∀ {A B} → RM A ⊢ B → LG · A · ⊢ · B ·
from↓  ax       = ⇀ ax⁺
from↓ (m□  f  ) = □ᴿ (↼ (□ᴸ (↽ (from↓ f))))
from↓ (m◇  f  ) = ◇ᴸ (⇀ (◇ᴿ (⇁ (from↓ f))))
from↓ (r□◇ f  ) = r□◇′ (from↓ f)
from↓ (r◇□ f  ) = r◇□′ (from↓ f)
from↓ (m⁰  f  ) = ⁰ᴿ (↼ (⁰ᴸ (⇁ (from↓ f))))
from↓ (m₀  f  ) = ₀ᴿ (↼ (₀ᴸ (⇁ (from↓ f))))
from↓ (r⁰₀ f  ) = r⁰₀′ (from↓ f)
from↓ (r₀⁰ f  ) = r₀⁰′ (from↓ f)
from↓ (m₁  f  ) = ₁ᴸ (⇀ (₁ᴿ (↽ (from↓ f))))
from↓ (m¹  f  ) = ¹ᴸ (⇀ (¹ᴿ (↽ (from↓ f))))
from↓ (r¹₁ f  ) = r¹₁′ (from↓ f)
from↓ (r₁¹ f  ) = r₁¹′ (from↓ f)
from↓ (m⊗  f g) = ⊗ᴸ (⇀ (⊗ᴿ (⇁ (from↓ f)) (⇁ (from↓ g))))
from↓ (m⇒  f g) = ⇒ᴿ (↼ (⇒ᴸ (⇁ (from↓ f)) (↽ (from↓ g))))
from↓ (m⇐  f g) = ⇐ᴿ (↼ (⇐ᴸ (⇁ (from↓ g)) (↽ (from↓ f))))
from↓ (r⇒⊗ f  ) = r⇒⊗′ (from↓ f)
from↓ (r⊗⇒ f  ) = r⊗⇒′ (from↓ f)
from↓ (r⇐⊗ f  ) = r⇐⊗′ (from↓ f)
from↓ (r⊗⇐ f  ) = r⊗⇐′ (from↓ f)
from↓ (m⊕  f g) = ⊕ᴿ (↼ (⊕ᴸ (↽ (from↓ f)) (↽ (from↓ g))))
from↓ (m⇛  f g) = ⇛ᴸ (⇀ (⇛ᴿ (⇁ (from↓ g)) (↽ (from↓ f))))
from↓ (m⇚  f g) = ⇚ᴸ (⇀ (⇚ᴿ (⇁ (from↓ f)) (↽ (from↓ g))))
from↓ (r⇛⊕ f  ) = r⇛⊕′ (from↓ f)
from↓ (r⊕⇛ f  ) = r⊕⇛′ (from↓ f)
from↓ (r⊕⇚ f  ) = r⊕⇚′ (from↓ f)
from↓ (r⇚⊕ f  ) = r⇚⊕′ (from↓ f)
from↓ (d⇛⇐ f  ) = d⇛⇐′ (from↓ f)
from↓ (d⇛⇒ f  ) = d⇛⇒′ (from↓ f)
from↓ (d⇚⇒ f  ) = d⇚⇒′ (from↓ f)
from↓ (d⇚⇐ f  ) = d⇚⇐′ (from↓ f)

eq↑ : ∀ {A B} → (RM A ⊢ B) ⇔ (LG ⟦ A ⟧⁺ ⊢ ⟦ B ⟧⁻)
eq↑ = equivalence from↑ (to ∘ deflate)

eq↓ : ∀ {A B} → (RM A ⊢ B) ⇔ (LG · A ·  ⊢ · B · )
eq↓ = equivalence from↓  to
