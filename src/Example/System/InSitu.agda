------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function            using (flip)
open import Data.Bool           using (Bool; true; false; not; _∧_; _∨_)


module Example.System.InSitu where


open import Data.Product        public using (_,_)
open import Example.System.Base public


-- * import focused Lambek-Grishin calculus
open import Logic.Translation
open import Logic.Intuitionistic.Ordered.InSitu Atom public
open import Logic.Intuitionistic.Ordered.InSitu.ToAgda Atom ⟦_⟧ᵁ using (InSitu→λΠ)
open Translation InSitu→λΠ public renaming ([_] to [_]ᵀ)


-- * create aliases for types
np n s : Type
np  = el NP
n   = el N
s   = el S


-- * setup lexicon
dutch : ⟦ n ⇐ n ⟧ᵀ
dutch p x = DUTCH x ∧ p x

english : ⟦ n ⇐ n ⟧ᵀ
english p x = ENGLISH x ∧ p x

smiles : ⟦ np ⇒ s ⟧ᵀ
smiles = SMILES

left : ⟦ np ⇒ s ⟧ᵀ
left = LEFT

cheats : ⟦ np ⇒ s ⟧ᵀ
cheats = CHEATS

teases : ⟦ (np ⇒ s) ⇐ np ⟧ᵀ
teases = flip TEASES

loves : ⟦ (np ⇒ s) ⇐ np ⟧ᵀ
loves = flip LOVES

thinks : ⟦ (np ⇒ s) ⇐ s ⟧ᵀ
thinks = flip SAID

everyone : ⟦ ◇ (s ⇦ □ (np ⇨ s)) ⟧ᵀ
everyone p = forAll (λ x → PERSON x ⊃ p x)

someone : ⟦ ◇ (s ⇦ □ (np ⇨ s)) ⟧ᵀ
someone p = exists (λ x → PERSON x ∧ p x)
