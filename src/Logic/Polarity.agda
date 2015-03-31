------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------

open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

module Logic.Polarity where


data Polarity : Set where
  + : Polarity
  - : Polarity


~_ : Polarity → Polarity
~ + = -
~ - = +


_≟-Polarity_ : (p₁ p₂ : Polarity) → Dec (p₁ ≡ p₂)
+ ≟-Polarity + = yes refl
- ≟-Polarity - = yes refl
+ ≟-Polarity - = no (λ ())
- ≟-Polarity + = no (λ ())


decSetoid : DecSetoid _ _
decSetoid = P.decSetoid _≟-Polarity_
