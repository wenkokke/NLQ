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


module Logic.LG.EquivalentToPol
  {ℓ} (Atom : Set ℓ) (Polarityᴬ? : Atom → Polarity) where


open import Logic.LG.Type.Polarised      Atom Polarityᴬ?
open import Logic.LG.Type                Atom
open import Logic.LG.Structure.Polarised Atom
open import Logic.LG.Sequent           Atom
open import Logic.LG.Base                Atom
open import Logic.LG.Pol.Base            Atom Polarityᴬ?


from : ∀ {J} → fLG J → LG J
from ax⁺       = ax⁺
from ax⁻       = ax⁻
from (⇁   f)   = ⇁   (from f)
from (↽   f)   = ↽   (from f)
from (⇀   f)   = ⇀   (from f)
from (↼   f)   = ↼   (from f)
from (◇L  f)   = ◇L  (from f)
from (◇R  f)   = ◇R  (from f)
from (□L  f)   = □L  (from f)
from (□R  f)   = □R  (from f)
from (₀L  f)   = ₀L  (from f)
from (₀R  f)   = ₀R  (from f)
from (⁰L  f)   = ⁰L  (from f)
from (⁰R  f)   = ⁰R  (from f)
from (₁L  f)   = ₁L  (from f)
from (₁R  f)   = ₁R  (from f)
from (¹L  f)   = ¹L  (from f)
from (¹R  f)   = ¹R  (from f)
from (⊗R  f g) = ⊗R  (from f) (from g)
from (⇚R  f g) = ⇚R  (from f) (from g)
from (⇛R  f g) = ⇛R  (from f) (from g)
from (⊕L  f g) = ⊕L  (from f) (from g)
from (⇒L  f g) = ⇒L  (from f) (from g)
from (⇐L  f g) = ⇐L  (from f) (from g)
from (⊗L  f)   = ⊗L  (from f)
from (⇚L  f)   = ⇚L  (from f)
from (⇛L  f)   = ⇛L  (from f)
from (⊕R  f)   = ⊕R  (from f)
from (⇒R  f)   = ⇒R  (from f)
from (⇐R  f)   = ⇐R  (from f)
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
