------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function            using (flip)
open import Data.Bool           using (Bool; true; false; not; _∧_; _∨_)


module Example.System.NLCL where


open import Data.Product        public using (_,_)
open import Example.System.Base public renaming (NP to DP)


-- * import focused Lambek-Grishin calculus
open import Logic.Translation
open import Logic.Intuitionistic.Ordered.NLCL Univ public
open import Logic.Intuitionistic.Ordered.NLCL.ToAgda Univ ⟦_⟧ᵁ using (NLCL→λΠ)
open Translation NLCL→λΠ public renaming ([_] to [_]ᵀ)


-- * create aliases for types
dp n s : Type
dp  = el DP
n   = el N
s   = el S


-- * setup lexicon
dutch : ⟦ n ⇐ n ⟧ᵀ
dutch p x = DUTCH x ∧ p x

english : ⟦ n ⇐ n ⟧ᵀ
english p x = ENGLISH x ∧ p x

smiles : ⟦ dp ⇒ s ⟧ᵀ
smiles = SMILES

left : ⟦ dp ⇒ s ⟧ᵀ
left = LEFT

cheats : ⟦ dp ⇒ s ⟧ᵀ
cheats = CHEATS

teases : ⟦ (dp ⇒ s) ⇐ dp ⟧ᵀ
teases = flip TEASES

loves : ⟦ (dp ⇒ s) ⇐ dp ⟧ᵀ
loves = flip LOVES

thinks : ⟦ (dp ⇒ s) ⇐ s ⟧ᵀ
thinks = flip WANTS

everyone : ⟦ s ⇦ (dp ⇨ s) ⟧ᵀ
everyone p = forAll (λ x → PERSON x ⊃ p x)

someone : ⟦ s ⇦ (dp ⇨ s) ⟧ᵀ
someone p = exists (λ x → PERSON x ∧ p x)
