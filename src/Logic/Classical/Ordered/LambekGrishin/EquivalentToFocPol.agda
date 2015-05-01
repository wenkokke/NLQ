------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Function.Equivalence                       using (_⇔_; equivalence)
open import Data.Product                               using (_×_; proj₁)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable                 using (fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


open import Logic.Polarity
open import Logic.Translation


module Logic.Classical.Ordered.LambekGrishin.EquivalentToFocPol {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised      (Polarity × Univ) proj₁
open import Logic.Classical.Ordered.LambekGrishin.Type                (Polarity × Univ)
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised (Polarity × Univ)
open import Logic.Classical.Ordered.LambekGrishin.Judgement           (Polarity × Univ)
open import Logic.Classical.Ordered.LambekGrishin.Base                (Polarity × Univ)
open import Logic.Classical.Ordered.LambekGrishin.FocPol.Base         Univ renaming (LG_ to LGᴾᴼᴸ_)


from : ∀ {J} → LGᴾᴼᴸ J → LG J
from ax⁺       = ax⁺
from ax⁻       = ax⁻
from (⇁   f)   = ⇁   (from f)
from (↽   f)   = ↽   (from f)
from (⇀   f)   = ⇀   (from f)
from (↼   f)   = ↼   (from f)
from (◇ᴸ  f)   = ◇ᴸ  (from f)
from (◇ᴿ  f)   = ◇ᴿ  (from f)
from (□ᴸ  f)   = □ᴸ  (from f)
from (□ᴿ  f)   = □ᴿ  (from f)
from (₀ᴸ  f)   = ₀ᴸ  (from f)
from (₀ᴿ  f)   = ₀ᴿ  (from f)
from (⁰ᴸ  f)   = ⁰ᴸ  (from f)
from (⁰ᴿ  f)   = ⁰ᴿ  (from f)
from (₁ᴸ  f)   = ₁ᴸ  (from f)
from (₁ᴿ  f)   = ₁ᴿ  (from f)
from (¹ᴸ  f)   = ¹ᴸ  (from f)
from (¹ᴿ  f)   = ¹ᴿ  (from f)
from (⊗ᴿ  f g) = ⊗ᴿ  (from f) (from g)
from (⇚ᴿ  f g) = ⇚ᴿ  (from f) (from g)
from (⇛ᴿ  f g) = ⇛ᴿ  (from f) (from g)
from (⊕ᴸ  f g) = ⊕ᴸ  (from f) (from g)
from (⇒ᴸ  f g) = ⇒ᴸ  (from f) (from g)
from (⇐ᴸ  f g) = ⇐ᴸ  (from f) (from g)
from (⊗ᴸ  f)   = ⊗ᴸ  (from f)
from (⇚ᴸ  f)   = ⇚ᴸ  (from f)
from (⇛ᴸ  f)   = ⇛ᴸ  (from f)
from (⊕ᴿ  f)   = ⊕ᴿ  (from f)
from (⇒ᴿ  f)   = ⇒ᴿ  (from f)
from (⇐ᴿ  f)   = ⇐ᴿ  (from f)
from (r□◇ f)   = r□◇ (from f)
from (r◇□ f)   = r◇□ (from f)
from (r⁰₀ f)   = r⁰₀ (from f)
from (r₀⁰ f)   = r₀⁰ (from f)
from (r¹₁ f)   = r¹₁ (from f)
from (r₁¹ f)   = r₁¹ (from f)
from (r⇒⊗ f)   = r⇒⊗ (from f)
from (r⊗⇒ f)   = r⊗⇒ (from f)
from (r⇐⊗ f)   = r⇐⊗ (from f)
from (r⊗⇐ f)   = r⊗⇐ (from f)
from (r⇚⊕ f)   = r⇚⊕ (from f)
from (r⊕⇚ f)   = r⊕⇚ (from f)
from (r⇛⊕ f)   = r⇛⊕ (from f)
from (r⊕⇛ f)   = r⊕⇛ (from f)
from (d⇛⇐ f)   = d⇛⇐ (from f)
from (d⇛⇒ f)   = d⇛⇒ (from f)
from (d⇚⇒ f)   = d⇚⇒ (from f)
from (d⇚⇐ f)   = d⇚⇐ (from f)
