------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function            using (id; flip)
open import Data.Bool           using (Bool; true; false; not; _∧_; _∨_)


module Example.System.aLG where


open import Data.Product        public using (_,_)
open import Example.System.Base public


-- * import focused Lambek-Grishin calculus
open import Logic.Translation
open import Logic.Classical.Ordered.LambekGrishin.ResMon        Univ public
open import Logic.Classical.Ordered.LambekGrishin.ResMon.ToAgda Univ Bool ⟦_⟧ᵁ using (CBV)
open Translation CBV public renaming ([_] to [_]ᵀ)


-- * create aliases for types
np n s⁻ : Type
np  = el NP
n   = el N
s⁻  = el S


-- * setup lexicon
dutch english : ⟦ n ⇐ n ⟧ᵀ
dutch   = λ {(k , p) → k (λ x → DUTCH   x ∧ p x)}
english = λ {(k , p) → k (λ x → ENGLISH x ∧ p x)}

smiles cheats left : ⟦ np ⇒ s⁻ ⟧ᵀ
smiles = λ {(x , k) → k (SMILES x)}
cheats = λ {(x , k) → k (CHEATS x)}
left   = λ {(x , k) → k (LEFT   x)}

teases loves : ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ
teases = λ {(k , y) → k (λ {(x , k′) → k′ (TEASES x y)})}
loves  = λ {(k , y) → k (λ {(x , k′) → k′ (LOVES  x y)})}

thinks : ⟦ (np ⇒ s⁻) ⇐ s⁻ ⟧ᵀ
thinks = λ {(k , y) → k (λ {(x , k′) → k′ (THINKS x y)})}

everyone someone : ⟦ s⁻ ⇚ (np ⇛ s⁻) ⟧ᵀ
everyone = true , (λ {(p , _) → forAll (λ x → PERSON x ⊃ p x)})
someone  = true , (λ {(p , _) → exists (λ x → PERSON x ∧ p x)})
