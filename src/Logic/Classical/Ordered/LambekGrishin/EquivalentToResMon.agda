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
open import Logic.Classical.Ordered.LambekGrishin.Type                Univ
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Univ as SS
open import Logic.Classical.Ordered.LambekGrishin.Judgement           Univ as SJ
open import Logic.Classical.Ordered.LambekGrishin.Base                Univ as SB renaming (LG_ to Str_)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement    Univ as AJ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base         Univ as AB renaming (LG_ to Alg_)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Trans        Univ as AT using ()
open import Logic.Classical.Ordered.LambekGrishin.ToResMon            Univ using (Str→Alg; ↓_)
open Translation Str→Alg renaming ([_] to to)


infix 5 ↑_


-- Inflate a type to its corresponding maximal structure.
↑_ : ∀ {p} → Type → Structure p
↑_ { - } (□   A) = [ ↑ A ]
↑_ { + } (◇   A) = ⟨ ↑ A ⟩
↑_ { - } (₀   A) = ₀ (↑ A)
↑_ { - } (A   ⁰) = (↑ A) ⁰
↑_ { + } (₁   A) = ₁ (↑ A)
↑_ { + } (A   ¹) = (↑ A) ¹
↑_ { + } (A ⊗ B) = (↑ A) ⊗ (↑ B)
↑_ { - } (A ⇒ B) = (↑ A) ⇒ (↑ B)
↑_ { - } (B ⇐ A) = (↑ B) ⇐ (↑ A)
↑_ { - } (B ⊕ A) = (↑ B) ⊕ (↑ A)
↑_ { + } (B ⇚ A) = (↑ B) ⇚ (↑ A)
↑_ { + } (A ⇛ B) = (↑ A) ⇛ (↑ B)
↑_ { _ } (  A  ) = · A ·


-- Once we inflate a type to a maximal structure, we can deflate the
-- structure back down to an elementary structure.
mutual
  deflateᴸ : ∀ {A Y} → Str ↑ A ⊢ Y → Str · A · ⊢ Y
  deflateᴸ {A = el  A} f = f
  deflateᴸ {A = □   A} f = f
  deflateᴸ {A = ◇   A} f = ◇ᴸ (r□◇ (deflateᴸ (r◇□ f)))
  deflateᴸ {A = ₀   A} f = f
  deflateᴸ {A = A   ⁰} f = f
  deflateᴸ {A = ₁   A} f = ₁ᴸ (r¹₁ (deflateᴿ (r₁¹ f)))
  deflateᴸ {A = A   ¹} f = ¹ᴸ (r₁¹ (deflateᴿ (r¹₁ f)))
  deflateᴸ {A = A ⇒ B} f = f
  deflateᴸ {A = A ⇐ B} f = f
  deflateᴸ {A = A ⇚ B} f = ⇚ᴸ (r⊕⇚ (deflateᴸ (r⇛⊕ (deflateᴿ (r⊕⇛ (r⇚⊕ f))))))
  deflateᴸ {A = A ⇛ B} f = ⇛ᴸ (r⊕⇛ (deflateᴸ (r⇚⊕ (deflateᴿ (r⊕⇚ (r⇛⊕ f))))))
  deflateᴸ {A = A ⊗ B} f = ⊗ᴸ (r⇐⊗ (deflateᴸ (r⊗⇐ (r⇒⊗ (deflateᴸ (r⊗⇒ f))))))
  deflateᴸ {A = A ⊕ B} f = f

  deflateᴿ : ∀ {X B} → Str X ⊢ ↑ B → Str X ⊢ · B ·
  deflateᴿ {B = el  B} f = f
  deflateᴿ {B = □   B} f = □ᴿ (r◇□ (deflateᴿ (r□◇ f)))
  deflateᴿ {B = ◇   B} f = f
  deflateᴿ {B = ₀   B} f = ₀ᴿ (r⁰₀ (deflateᴸ (r₀⁰ f)))
  deflateᴿ {B = B   ⁰} f = ⁰ᴿ (r₀⁰ (deflateᴸ (r⁰₀ f)))
  deflateᴿ {B = ₁   B} f = f
  deflateᴿ {B = B   ¹} f = f
  deflateᴿ {B = B ⇒ C} f = ⇒ᴿ (r⊗⇒ (deflateᴿ (r⇐⊗ (deflateᴸ (r⊗⇐ (r⇒⊗ f))))))
  deflateᴿ {B = B ⇐ C} f = ⇐ᴿ (r⊗⇐ (deflateᴿ (r⇒⊗ (deflateᴸ (r⊗⇒ (r⇐⊗ f))))))
  deflateᴿ {B = B ⇚ C} f = f
  deflateᴿ {B = B ⇛ C} f = f
  deflateᴿ {B = B ⊗ C} f = f
  deflateᴿ {B = B ⊕ C} f = ⊕ᴿ (r⇚⊕ (deflateᴿ (r⊕⇚ (r⇛⊕ (deflateᴿ (r⊕⇛ f))))))


deflate : ∀ {A B} → Str ↑ A ⊢ ↑ B → Str · A · ⊢ · B ·
deflate = deflateᴸ ∘ deflateᴿ



-- Using deflation, we can define our first version of importing
-- proofs from the algebraic axiomatisation of LG, inflating the types
-- into their corresponding maximal structures.
from↑ : ∀ {A B} → Alg A ⊢ B → Str ↑ A ⊢ ↑ B
from↑ (ax     ) = ⇀ ax⁺
from↑ (m□  f  ) = ↼ (□ᴸ (↽ (deflateᴸ (from↑ f))))
from↑ (m◇  f  ) = ⇀ (◇ᴿ (⇁ (deflateᴿ (from↑ f))))
from↑ (m₀  f  ) = ↼ (₀ᴸ (⇁ (deflateᴿ (from↑ f))))
from↑ (m⁰  f  ) = ↼ (⁰ᴸ (⇁ (deflateᴿ (from↑ f))))
from↑ (m₁  f  ) = ⇀ (₁ᴿ (↽ (deflateᴸ (from↑ f))))
from↑ (m¹  f  ) = ⇀ (¹ᴿ (↽ (deflateᴸ (from↑ f))))
from↑ (m⊗  f g) = ⇀ (⊗ᴿ (⇁ (deflateᴿ (from↑ f))) (⇁ (deflateᴿ (from↑ g))))
from↑ (m⇒  f g) = ↼ (⇒ᴸ (⇁ (deflateᴿ (from↑ f))) (↽ (deflateᴸ (from↑ g))))
from↑ (m⇐  f g) = ↼ (⇐ᴸ (⇁ (deflateᴿ (from↑ g))) (↽ (deflateᴸ (from↑ f))))
from↑ (m⊕  f g) = ↼ (⊕ᴸ (↽ (deflateᴸ (from↑ f))) (↽ (deflateᴸ (from↑ g))))
from↑ (m⇛  f g) = ⇀ (⇛ᴿ (⇁ (deflateᴿ (from↑ g))) (↽ (deflateᴸ (from↑ f))))
from↑ (m⇚  f g) = ⇀ (⇚ᴿ (⇁ (deflateᴿ (from↑ f))) (↽ (deflateᴸ (from↑ g))))
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


eq↑ : ∀ {A B} → (Alg A ⊢ B) ⇔ (Str ↑ A ⊢ ↑ B)
eq↑ = equivalence from↑ (to ∘ deflate)



-- Alternatively, if we know that a type comes from a deflated
-- structure, we can maximally inflate the structure, and then deflate
-- it down to the original structure.
mutual
  inflateᴸ : ∀ {X Y} → Str ↑ ↓ X ⊢ Y → Str X ⊢ Y
  inflateᴸ {X = · A ·} f = deflateᴸ f
  inflateᴸ {X = ⟨ X ⟩} f = r□◇ (inflateᴸ (r◇□ f))
  inflateᴸ {X = ₁   X} f = r¹₁ (inflateᴿ (r₁¹ f))
  inflateᴸ {X = X   ¹} f = r₁¹ (inflateᴿ (r¹₁ f))
  inflateᴸ {X = X ⊗ Y} f = r⇐⊗ (inflateᴸ (r⊗⇐ (r⇒⊗ (inflateᴸ (r⊗⇒ f)))))
  inflateᴸ {X = X ⇚ Y} f = r⊕⇚ (inflateᴸ (r⇛⊕ (inflateᴿ (r⊕⇛ (r⇚⊕ f)))))
  inflateᴸ {X = X ⇛ Y} f = r⊕⇛ (inflateᴸ (r⇚⊕ (inflateᴿ (r⊕⇚ (r⇛⊕ f)))))

  inflateᴿ : ∀ {X Y} → Str X ⊢ ↑ ↓ Y → Str X ⊢ Y
  inflateᴿ {Y = · A ·} f = deflateᴿ f
  inflateᴿ {Y = [ Y ]} f = r◇□ (inflateᴿ (r□◇ f))
  inflateᴿ {Y = ₀   Y} f = r⁰₀ (inflateᴸ (r₀⁰ f))
  inflateᴿ {Y = Y   ⁰} f = r₀⁰ (inflateᴸ (r⁰₀ f))
  inflateᴿ {Y = X ⊕ Y} f = r⇛⊕ (inflateᴿ (r⊕⇛ (r⇚⊕ (inflateᴿ (r⊕⇚ f)))))
  inflateᴿ {Y = X ⇒ Y} f = r⊗⇒ (inflateᴿ (r⇐⊗ (inflateᴸ (r⊗⇐ (r⇒⊗ f)))))
  inflateᴿ {Y = X ⇐ Y} f = r⊗⇐ (inflateᴿ (r⇒⊗ (inflateᴸ (r⊗⇒ (r⇐⊗ f)))))


inflate : ∀ {X Y} → Str ↑ ↓ X ⊢ ↑ ↓ Y → Str X ⊢ Y
inflate = inflateᴸ ∘ inflateᴿ



-- Using the deflate/inflate approach, we can import theorems from the
-- algebraic axiomatisation---for instance, admissible transitivity.
trans′ : ∀ {X A Y} → Str X ⊢[ A ] → Str [ A ]⊢ Y → Str X ⊢ Y
trans′ f g = inflate (from↑ (AT.trans′ (to f) (to g)))



-- Using transitivity, we can define the inverted versions of the
-- invertable structural rules, which reintroduce structures.
◇ᴸ′ : ∀ {Y A} → Str · ◇ A · ⊢ Y → Str ⟨ · A · ⟩ ⊢ Y
◇ᴸ′ f = trans′ (◇ᴿ ax⁺) (↽ f)

□ᴿ′ : ∀ {X A} → Str X ⊢ · □ A · → Str X ⊢ [ · A · ]
□ᴿ′ f = trans′ (⇁ f) (□ᴸ ax⁻)

₀ᴿ′ : ∀ {X A} → Str X ⊢ · ₀ A · → Str X ⊢ ₀ · A ·
₀ᴿ′ f = trans′ (⇁ f) (₀ᴸ ax⁺)

⁰ᴿ′ : ∀ {X A} → Str X ⊢ · A ⁰ · → Str X ⊢ · A · ⁰
⁰ᴿ′ f = trans′ (⇁ f) (⁰ᴸ ax⁺)

₁ᴸ′ : ∀ {Y A} → Str · ₁ A · ⊢ Y → Str ₁ · A · ⊢ Y
₁ᴸ′ f = trans′ (₁ᴿ ax⁻) (↽ f)

¹ᴸ′ : ∀ {Y A} → Str · A ¹ · ⊢ Y → Str · A · ¹ ⊢ Y
¹ᴸ′ f = trans′ (¹ᴿ ax⁻) (↽ f)

⊗ᴸ′ : ∀ {Y A B} → Str · A ⊗ B · ⊢ Y → Str · A · ⊗ · B · ⊢ Y
⊗ᴸ′ f = trans′ (⊗ᴿ ax⁺ ax⁺) (↽ f)

⇒ᴿ′ : ∀ {X A B} → Str X ⊢ · A ⇒ B · → Str X ⊢ · A · ⇒ · B ·
⇒ᴿ′ f = trans′ (⇁ f) (⇒ᴸ ax⁺ ax⁻)

⇐ᴿ′ : ∀ {X A B} → Str X ⊢ · B ⇐ A · → Str X ⊢ · B · ⇐ · A ·
⇐ᴿ′ f = trans′ (⇁ f) (⇐ᴸ ax⁺ ax⁻)

⊕ᴿ′ : ∀ {X A B} → Str X ⊢ · B ⊕ A · → Str X ⊢ · B · ⊕ · A ·
⊕ᴿ′ f = trans′ (⇁ f) (⊕ᴸ ax⁻ ax⁻)

⇚ᴸ′ : ∀ {X A B} → Str · A ⇚ B · ⊢ X → Str · A · ⇚ · B · ⊢ X
⇚ᴸ′ f = trans′ (⇚ᴿ ax⁺ ax⁻) (↽ f)

⇛ᴸ′ : ∀ {X A B} → Str · B ⇛ A · ⊢ X → Str · B · ⇛ · A · ⊢ X
⇛ᴸ′ f = trans′ (⇛ᴿ ax⁺ ax⁻) (↽ f)


-- In addition, we can use these invertable rules to define the
-- algebraic versions of the residuation and distribution
-- rules--i.e. those which work on elementary structures.
r□◇′ : ∀ {A B} → Str · A · ⊢ · □ B · → Str · ◇ A · ⊢ · B ·
r□◇′ f = ◇ᴸ (r□◇ (□ᴿ′ f))

r◇□′ : ∀ {A B} → Str · ◇ A · ⊢ · B · → Str · A · ⊢ · □ B ·
r◇□′ f = □ᴿ (r◇□ (◇ᴸ′ f))

r⁰₀′ : ∀ {A B} → Str · A · ⊢ · B ⁰ · → Str · B · ⊢ · ₀ A ·
r⁰₀′ f = ₀ᴿ (r⁰₀ (⁰ᴿ′ f))

r₀⁰′ : ∀ {A B} → Str · B · ⊢ · ₀ A · → Str · A · ⊢ · B ⁰ ·
r₀⁰′ f = ⁰ᴿ (r₀⁰ (₀ᴿ′ f))

r¹₁′ : ∀ {A B} → Str · A ¹ · ⊢ · B · → Str · ₁ B · ⊢ · A ·
r¹₁′ f = ₁ᴸ (r¹₁ (¹ᴸ′ f))

r₁¹′ : ∀ {A B} → Str · ₁ B · ⊢ · A · → Str · A ¹ · ⊢ · B ·
r₁¹′ f = ¹ᴸ (r₁¹ (₁ᴸ′ f))

r⇒⊗′ : ∀ {A B C} → Str · B · ⊢ · A ⇒ C · → Str · A ⊗ B · ⊢ · C ·
r⇒⊗′ f = ⊗ᴸ (r⇒⊗ (⇒ᴿ′ f))

r⊗⇒′ : ∀ {A B C} → Str · A ⊗ B · ⊢ · C · → Str · B · ⊢ · A ⇒ C ·
r⊗⇒′ f = ⇒ᴿ (r⊗⇒ (⊗ᴸ′ f))

r⇐⊗′ : ∀ {A B C} → Str · A · ⊢ · C ⇐ B · → Str · A ⊗ B · ⊢ · C ·
r⇐⊗′ f = ⊗ᴸ (r⇐⊗ (⇐ᴿ′ f))

r⊗⇐′ : ∀ {A B C} → Str · A ⊗ B · ⊢ · C · → Str · A · ⊢ · C ⇐ B ·
r⊗⇐′ f = ⇐ᴿ (r⊗⇐ (⊗ᴸ′ f))

r⇚⊕′ : ∀ {A B C} → Str · C ⇚ A · ⊢ · B · → Str · C · ⊢ · B ⊕ A ·
r⇚⊕′ f = ⊕ᴿ (r⇚⊕ (⇚ᴸ′ f))

r⊕⇚′ : ∀ {A B C} → Str · C · ⊢ · B ⊕ A · → Str · C ⇚ A · ⊢ · B ·
r⊕⇚′ f = ⇚ᴸ (r⊕⇚ (⊕ᴿ′ f))

r⇛⊕′ : ∀ {A B C} → Str · B ⇛ C · ⊢ · A · → Str · C · ⊢ · B ⊕ A ·
r⇛⊕′ f = ⊕ᴿ (r⇛⊕ (⇛ᴸ′ f))

r⊕⇛′ : ∀ {A B C} → Str · C · ⊢ · B ⊕ A · → Str · B ⇛ C · ⊢ · A ·
r⊕⇛′ f = ⇛ᴸ (r⊕⇛ (⊕ᴿ′ f))

d⇛⇐′ : ∀ {A B C D} → Str · A ⊗ B · ⊢ · C ⊕ D · → Str · C ⇛ A · ⊢ · D ⇐ B ·
d⇛⇐′ f = ⇐ᴿ (⇛ᴸ (d⇛⇐ (⊗ᴸ′ (⊕ᴿ′ f))))

d⇛⇒′ : ∀ {A B C D} → Str · A ⊗ B · ⊢ · C ⊕ D · → Str · C ⇛ B · ⊢ · A ⇒ D ·
d⇛⇒′ f = ⇒ᴿ (⇛ᴸ (d⇛⇒ (⊗ᴸ′ (⊕ᴿ′ f))))

d⇚⇒′ : ∀ {A B C D} → Str · A ⊗ B · ⊢ · C ⊕ D · → Str · B ⇚ D · ⊢ · A ⇒ C ·
d⇚⇒′ f = ⇒ᴿ (⇚ᴸ (d⇚⇒ (⊗ᴸ′ (⊕ᴿ′ f))))

d⇚⇐′ : ∀ {A B C D} → Str · A ⊗ B · ⊢ · C ⊕ D · → Str · A ⇚ D · ⊢ · C ⇐ B ·
d⇚⇐′ f = ⇐ᴿ (⇚ᴸ (d⇚⇐ (⊗ᴸ′ (⊕ᴿ′ f))))



-- Lastly, using these rules, we can define a second equivalence
-- between the algebraic and the structured versions of LG, namely one
-- which converts theorems in the algebraic system to algebraic
-- theorems in the structured system.
-- This equivalence is preferred, since there is no need to convert
-- between types and structures.
from↓ : ∀ {A B} → Alg A ⊢ B → Str · A · ⊢ · B ·
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


eq↓ : ∀ {A B} → (Alg A ⊢ B) ⇔ (Str · A ·  ⊢ · B · )
eq↓ = equivalence from↓ to
