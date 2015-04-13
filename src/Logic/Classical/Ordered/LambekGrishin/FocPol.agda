------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level                                      using (suc; _⊔_)
open import Function                                   using (id; _∘_)
open import Function.Equivalence                       using (_⇔_; equivalence)
open import Data.Product                               using (_×_; proj₁)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable                 using (fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


open import Logic.Polarity
open import Logic.Translation


module Logic.Classical.Ordered.LambekGrishin.FocPol {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (⟦_⟧ᵁ : Univ → Set ℓ₂) (⊥ : Univ) where


-- * import fLG
open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised (Polarity × Univ) proj₁ public
     hiding (module Correct; module Polarised; Polarised)
open import Logic.Classical.Ordered.LambekGrishin.Type (Polarity × Univ) public
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised (Polarity × Univ) public
     hiding (module Correct; module Polarised; Polarised)
open import Logic.Classical.Ordered.LambekGrishin.Judgement (Polarity × Univ) public
open import Logic.Classical.Ordered.LambekGrishin.FocPol.Base Univ public


-- * import translation from fLG into Agda
open import Logic.Classical.Ordered.LambekGrishin.FocPol.ToIntuitionisticLinearLambda Univ ⊥ using (Ord→Lin)
open import Logic.Intuitionistic.Linear.Lambda.ToUnrestricted Univ using (Lin→Un)
open import Logic.Intuitionistic.Unrestricted.Lambda.ToAgda Univ ⟦_⟧ᵁ using (Un→Agda)
open import Logic.Intuitionistic.Unrestricted.Agda.Environment public

open Translation (Un→Agda ◇ Lin→Un ◇ Ord→Lin) public renaming ([_] to [_]ᵀ)
