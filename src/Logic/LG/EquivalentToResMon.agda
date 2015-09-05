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


open import Function                                   using (_∘_; id)
open import Function.Equivalence                       using (_⇔_; equivalence)
open import Data.Product                               using (_×_; _,_; proj₂)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable                 using (fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module Logic.LG.EquivalentToResMon {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.LG.Type                Atom
open import Logic.LG.Structure.Polarised Atom as SS
open import Logic.LG.Sequent           Atom as SJ
open import Logic.LG.Base                Atom as SB renaming (LG_ to Str_)
open import Logic.LG.ResMon.Sequent    Atom as AJ
open import Logic.LG.ResMon.Base         Atom as AB renaming (LG_ to Alg_)
open import Logic.LG.ResMon.Cut          Atom as AT using ()
open import Logic.LG.ToResMon            Atom public
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
  deflateL : ∀ {A Y} → Str ↑ A ⊢ Y → Str · A · ⊢ Y
  deflateL {A = el  A} f = f
  deflateL {A = □   A} f = f
  deflateL {A = ◇   A} f = ◇L (r□◇ (deflateL (r◇□ f)))
  deflateL {A = ₀   A} f = f
  deflateL {A = A   ⁰} f = f
  deflateL {A = ₁   A} f = ₁L (r¹₁ (deflateR (r₁¹ f)))
  deflateL {A = A   ¹} f = ¹L (r₁¹ (deflateR (r¹₁ f)))
  deflateL {A = A ⇒ B} f = f
  deflateL {A = A ⇐ B} f = f
  deflateL {A = A ⇚ B} f = ⇚L (r⊕⇚ (deflateL (r⇛⊕ (deflateR (r⊕⇛ (r⇚⊕ f))))))
  deflateL {A = A ⇛ B} f = ⇛L (r⊕⇛ (deflateL (r⇚⊕ (deflateR (r⊕⇚ (r⇛⊕ f))))))
  deflateL {A = A ⊗ B} f = ⊗L (r⇐⊗ (deflateL (r⊗⇐ (r⇒⊗ (deflateL (r⊗⇒ f))))))
  deflateL {A = A ⊕ B} f = f

  deflateR : ∀ {X B} → Str X ⊢ ↑ B → Str X ⊢ · B ·
  deflateR {B = el  B} f = f
  deflateR {B = □   B} f = □R (r◇□ (deflateR (r□◇ f)))
  deflateR {B = ◇   B} f = f
  deflateR {B = ₀   B} f = ₀R (r⁰₀ (deflateL (r₀⁰ f)))
  deflateR {B = B   ⁰} f = ⁰R (r₀⁰ (deflateL (r⁰₀ f)))
  deflateR {B = ₁   B} f = f
  deflateR {B = B   ¹} f = f
  deflateR {B = B ⇒ C} f = ⇒R (r⊗⇒ (deflateR (r⇐⊗ (deflateL (r⊗⇐ (r⇒⊗ f))))))
  deflateR {B = B ⇐ C} f = ⇐R (r⊗⇐ (deflateR (r⇒⊗ (deflateL (r⊗⇒ (r⇐⊗ f))))))
  deflateR {B = B ⇚ C} f = f
  deflateR {B = B ⇛ C} f = f
  deflateR {B = B ⊗ C} f = f
  deflateR {B = B ⊕ C} f = ⊕R (r⇚⊕ (deflateR (r⊕⇚ (r⇛⊕ (deflateR (r⊕⇛ f))))))


deflate : ∀ {A B} → Str ↑ A ⊢ ↑ B → Str · A · ⊢ · B ·
deflate = deflateL ∘ deflateR



-- Using deflation, we can define our first version of importing
-- proofs from the algebraic axiomatisation of LG, inflating the types
-- into their corresponding maximal structures.
from↑ : ∀ {A B} → Alg A ⊢ B → Str ↑ A ⊢ ↑ B
from↑ (ax     ) = ⇀ ax⁺
from↑ (m□  f  ) = ↼ (□L (↽ (deflateL (from↑ f))))
from↑ (m◇  f  ) = ⇀ (◇R (⇁ (deflateR (from↑ f))))
from↑ (m₀  f  ) = ↼ (₀L (⇁ (deflateR (from↑ f))))
from↑ (m⁰  f  ) = ↼ (⁰L (⇁ (deflateR (from↑ f))))
from↑ (m₁  f  ) = ⇀ (₁R (↽ (deflateL (from↑ f))))
from↑ (m¹  f  ) = ⇀ (¹R (↽ (deflateL (from↑ f))))
from↑ (m⊗  f g) = ⇀ (⊗R (⇁ (deflateR (from↑ f))) (⇁ (deflateR (from↑ g))))
from↑ (m⇒  f g) = ↼ (⇒L (⇁ (deflateR (from↑ f))) (↽ (deflateL (from↑ g))))
from↑ (m⇐  f g) = ↼ (⇐L (⇁ (deflateR (from↑ g))) (↽ (deflateL (from↑ f))))
from↑ (m⊕  f g) = ↼ (⊕L (↽ (deflateL (from↑ f))) (↽ (deflateL (from↑ g))))
from↑ (m⇛  f g) = ⇀ (⇛R (⇁ (deflateR (from↑ g))) (↽ (deflateL (from↑ f))))
from↑ (m⇚  f g) = ⇀ (⇚R (⇁ (deflateR (from↑ f))) (↽ (deflateL (from↑ g))))
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

Alg→Str↑ : Translation Type Type Alg_ Str_
Alg→Str↑ = record { ⟦_⟧ᵗ = id ; ⟦_⟧ʲ = λ {(A ⊢ B) → ↑ A ⊢ ↑ B} ; [_] = λ { {A ⊢ B} → from↑} }


-- Alternatively, if we know that a type comes from a deflated
-- structure, we can maximally inflate the structure, and then deflate
-- it down to the original structure.
mutual
  inflateL : ∀ {X Y} → Str ↑ ↓ X ⊢ Y → Str X ⊢ Y
  inflateL {X = · A ·} f = deflateL f
  inflateL {X = ⟨ X ⟩} f = r□◇ (inflateL (r◇□ f))
  inflateL {X = ₁   X} f = r¹₁ (inflateR (r₁¹ f))
  inflateL {X = X   ¹} f = r₁¹ (inflateR (r¹₁ f))
  inflateL {X = X ⊗ Y} f = r⇐⊗ (inflateL (r⊗⇐ (r⇒⊗ (inflateL (r⊗⇒ f)))))
  inflateL {X = X ⇚ Y} f = r⊕⇚ (inflateL (r⇛⊕ (inflateR (r⊕⇛ (r⇚⊕ f)))))
  inflateL {X = X ⇛ Y} f = r⊕⇛ (inflateL (r⇚⊕ (inflateR (r⊕⇚ (r⇛⊕ f)))))

  inflateR : ∀ {X Y} → Str X ⊢ ↑ ↓ Y → Str X ⊢ Y
  inflateR {Y = · A ·} f = deflateR f
  inflateR {Y = [ Y ]} f = r◇□ (inflateR (r□◇ f))
  inflateR {Y = ₀   Y} f = r⁰₀ (inflateL (r₀⁰ f))
  inflateR {Y = Y   ⁰} f = r₀⁰ (inflateL (r⁰₀ f))
  inflateR {Y = X ⊕ Y} f = r⇛⊕ (inflateR (r⊕⇛ (r⇚⊕ (inflateR (r⊕⇚ f)))))
  inflateR {Y = X ⇒ Y} f = r⊗⇒ (inflateR (r⇐⊗ (inflateL (r⊗⇐ (r⇒⊗ f)))))
  inflateR {Y = X ⇐ Y} f = r⊗⇐ (inflateR (r⇒⊗ (inflateL (r⊗⇒ (r⇐⊗ f)))))


inflate : ∀ {X Y} → Str ↑ ↓ X ⊢ ↑ ↓ Y → Str X ⊢ Y
inflate = inflateL ∘ inflateR



-- Using the deflate/inflate approach, we can import theorems from the
-- algebraic axiomatisation---for instance, admissible transitivity.
cut′ : ∀ {X A Y} → Str X ⊢[ A ] → Str [ A ]⊢ Y → Str X ⊢ Y
cut′ f g = inflate (from↑ (AT.cut′ (to f) (to g)))



-- Using transitivity, we can define the inverted versions of the
-- invertable structural rules, which reintroduce structures.
◇L′ : ∀ {Y A} → Str · ◇ A · ⊢ Y → Str ⟨ · A · ⟩ ⊢ Y
◇L′ f = cut′ (◇R ax⁺) (↽ f)

□R′ : ∀ {X A} → Str X ⊢ · □ A · → Str X ⊢ [ · A · ]
□R′ f = cut′ (⇁ f) (□L ax⁻)

₀R′ : ∀ {X A} → Str X ⊢ · ₀ A · → Str X ⊢ ₀ · A ·
₀R′ f = cut′ (⇁ f) (₀L ax⁺)

⁰R′ : ∀ {X A} → Str X ⊢ · A ⁰ · → Str X ⊢ · A · ⁰
⁰R′ f = cut′ (⇁ f) (⁰L ax⁺)

₁L′ : ∀ {Y A} → Str · ₁ A · ⊢ Y → Str ₁ · A · ⊢ Y
₁L′ f = cut′ (₁R ax⁻) (↽ f)

¹L′ : ∀ {Y A} → Str · A ¹ · ⊢ Y → Str · A · ¹ ⊢ Y
¹L′ f = cut′ (¹R ax⁻) (↽ f)

⊗L′ : ∀ {Y A B} → Str · A ⊗ B · ⊢ Y → Str · A · ⊗ · B · ⊢ Y
⊗L′ f = cut′ (⊗R ax⁺ ax⁺) (↽ f)

⇒R′ : ∀ {X A B} → Str X ⊢ · A ⇒ B · → Str X ⊢ · A · ⇒ · B ·
⇒R′ f = cut′ (⇁ f) (⇒L ax⁺ ax⁻)

⇐R′ : ∀ {X A B} → Str X ⊢ · B ⇐ A · → Str X ⊢ · B · ⇐ · A ·
⇐R′ f = cut′ (⇁ f) (⇐L ax⁺ ax⁻)

⊕R′ : ∀ {X A B} → Str X ⊢ · B ⊕ A · → Str X ⊢ · B · ⊕ · A ·
⊕R′ f = cut′ (⇁ f) (⊕L ax⁻ ax⁻)

⇚L′ : ∀ {X A B} → Str · A ⇚ B · ⊢ X → Str · A · ⇚ · B · ⊢ X
⇚L′ f = cut′ (⇚R ax⁺ ax⁻) (↽ f)

⇛L′ : ∀ {X A B} → Str · B ⇛ A · ⊢ X → Str · B · ⇛ · A · ⊢ X
⇛L′ f = cut′ (⇛R ax⁺ ax⁻) (↽ f)


-- In addition, we can use these invertable rules to define the
-- algebraic versions of the residuation and distribution
-- rules--i.e. those which work on elementary structures.
r□◇′ : ∀ {A B} → Str · A · ⊢ · □ B · → Str · ◇ A · ⊢ · B ·
r□◇′ f = ◇L (r□◇ (□R′ f))

r◇□′ : ∀ {A B} → Str · ◇ A · ⊢ · B · → Str · A · ⊢ · □ B ·
r◇□′ f = □R (r◇□ (◇L′ f))

r⁰₀′ : ∀ {A B} → Str · A · ⊢ · B ⁰ · → Str · B · ⊢ · ₀ A ·
r⁰₀′ f = ₀R (r⁰₀ (⁰R′ f))

r₀⁰′ : ∀ {A B} → Str · B · ⊢ · ₀ A · → Str · A · ⊢ · B ⁰ ·
r₀⁰′ f = ⁰R (r₀⁰ (₀R′ f))

r¹₁′ : ∀ {A B} → Str · A ¹ · ⊢ · B · → Str · ₁ B · ⊢ · A ·
r¹₁′ f = ₁L (r¹₁ (¹L′ f))

r₁¹′ : ∀ {A B} → Str · ₁ B · ⊢ · A · → Str · A ¹ · ⊢ · B ·
r₁¹′ f = ¹L (r₁¹ (₁L′ f))

r⇒⊗′ : ∀ {A B C} → Str · B · ⊢ · A ⇒ C · → Str · A ⊗ B · ⊢ · C ·
r⇒⊗′ f = ⊗L (r⇒⊗ (⇒R′ f))

r⊗⇒′ : ∀ {A B C} → Str · A ⊗ B · ⊢ · C · → Str · B · ⊢ · A ⇒ C ·
r⊗⇒′ f = ⇒R (r⊗⇒ (⊗L′ f))

r⇐⊗′ : ∀ {A B C} → Str · A · ⊢ · C ⇐ B · → Str · A ⊗ B · ⊢ · C ·
r⇐⊗′ f = ⊗L (r⇐⊗ (⇐R′ f))

r⊗⇐′ : ∀ {A B C} → Str · A ⊗ B · ⊢ · C · → Str · A · ⊢ · C ⇐ B ·
r⊗⇐′ f = ⇐R (r⊗⇐ (⊗L′ f))

r⇚⊕′ : ∀ {A B C} → Str · C ⇚ A · ⊢ · B · → Str · C · ⊢ · B ⊕ A ·
r⇚⊕′ f = ⊕R (r⇚⊕ (⇚L′ f))

r⊕⇚′ : ∀ {A B C} → Str · C · ⊢ · B ⊕ A · → Str · C ⇚ A · ⊢ · B ·
r⊕⇚′ f = ⇚L (r⊕⇚ (⊕R′ f))

r⇛⊕′ : ∀ {A B C} → Str · B ⇛ C · ⊢ · A · → Str · C · ⊢ · B ⊕ A ·
r⇛⊕′ f = ⊕R (r⇛⊕ (⇛L′ f))

r⊕⇛′ : ∀ {A B C} → Str · C · ⊢ · B ⊕ A · → Str · B ⇛ C · ⊢ · A ·
r⊕⇛′ f = ⇛L (r⊕⇛ (⊕R′ f))

d⇛⇐′ : ∀ {A B C D} → Str · A ⊗ B · ⊢ · C ⊕ D · → Str · C ⇛ A · ⊢ · D ⇐ B ·
d⇛⇐′ f = ⇐R (⇛L (d⇛⇐ (⊗L′ (⊕R′ f))))

d⇛⇒′ : ∀ {A B C D} → Str · A ⊗ B · ⊢ · C ⊕ D · → Str · C ⇛ B · ⊢ · A ⇒ D ·
d⇛⇒′ f = ⇒R (⇛L (d⇛⇒ (⊗L′ (⊕R′ f))))

d⇚⇒′ : ∀ {A B C D} → Str · A ⊗ B · ⊢ · C ⊕ D · → Str · B ⇚ D · ⊢ · A ⇒ C ·
d⇚⇒′ f = ⇒R (⇚L (d⇚⇒ (⊗L′ (⊕R′ f))))

d⇚⇐′ : ∀ {A B C D} → Str · A ⊗ B · ⊢ · C ⊕ D · → Str · A ⇚ D · ⊢ · C ⇐ B ·
d⇚⇐′ f = ⇐R (⇚L (d⇚⇐ (⊗L′ (⊕R′ f))))



-- Lastly, using these rules, we can define a second equivalence
-- between the algebraic and the structured versions of LG, namely one
-- which converts theorems in the algebraic system to algebraic
-- theorems in the structured system.
-- This equivalence is preferred, since there is no need to convert
-- between types and structures.
from↓ : ∀ {A B} → Alg A ⊢ B → Str · A · ⊢ · B ·
from↓  ax       = ⇀ ax⁺
from↓ (m□  f  ) = □R (↼ (□L (↽ (from↓ f))))
from↓ (m◇  f  ) = ◇L (⇀ (◇R (⇁ (from↓ f))))
from↓ (r□◇ f  ) = r□◇′ (from↓ f)
from↓ (r◇□ f  ) = r◇□′ (from↓ f)
from↓ (m⁰  f  ) = ⁰R (↼ (⁰L (⇁ (from↓ f))))
from↓ (m₀  f  ) = ₀R (↼ (₀L (⇁ (from↓ f))))
from↓ (r⁰₀ f  ) = r⁰₀′ (from↓ f)
from↓ (r₀⁰ f  ) = r₀⁰′ (from↓ f)
from↓ (m₁  f  ) = ₁L (⇀ (₁R (↽ (from↓ f))))
from↓ (m¹  f  ) = ¹L (⇀ (¹R (↽ (from↓ f))))
from↓ (r¹₁ f  ) = r¹₁′ (from↓ f)
from↓ (r₁¹ f  ) = r₁¹′ (from↓ f)
from↓ (m⊗  f g) = ⊗L (⇀ (⊗R (⇁ (from↓ f)) (⇁ (from↓ g))))
from↓ (m⇒  f g) = ⇒R (↼ (⇒L (⇁ (from↓ f)) (↽ (from↓ g))))
from↓ (m⇐  f g) = ⇐R (↼ (⇐L (⇁ (from↓ g)) (↽ (from↓ f))))
from↓ (r⇒⊗ f  ) = r⇒⊗′ (from↓ f)
from↓ (r⊗⇒ f  ) = r⊗⇒′ (from↓ f)
from↓ (r⇐⊗ f  ) = r⇐⊗′ (from↓ f)
from↓ (r⊗⇐ f  ) = r⊗⇐′ (from↓ f)
from↓ (m⊕  f g) = ⊕R (↼ (⊕L (↽ (from↓ f)) (↽ (from↓ g))))
from↓ (m⇛  f g) = ⇛L (⇀ (⇛R (⇁ (from↓ g)) (↽ (from↓ f))))
from↓ (m⇚  f g) = ⇚L (⇀ (⇚R (⇁ (from↓ f)) (↽ (from↓ g))))
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

Alg→Str↓ : Translation Type Type Alg_ Str_
Alg→Str↓ = record { ⟦_⟧ᵗ = id ; ⟦_⟧ʲ = λ {(A ⊢ B) → · A · ⊢ · B ·} ; [_] = λ { {A ⊢ B} → from↓} }
