------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                              using (id; const)
open import Data.Bool                             using (Bool; true; false; not; _∧_; _∨_)
open import Data.List                             using (List; _∷_; []; map; foldr)
open import Data.Product                          using (_×_; proj₁; _,_)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Example.System.fLG where


open import Example.System.Base public


-- * import focused Lambek-Grishin calculus
open import Logic.Translation
open import Logic.Polarity public
open import Logic.Classical.Ordered.LambekGrishin.FocPol Univ public
open import Logic.Classical.Ordered.LambekGrishin.FocPol.ToIntuitionisticLinearLambda Univ S using (LG→LL)
open import Logic.Intuitionistic.Linear.Lambda.ToUnrestricted Univ using (LL→Λ)
open import Logic.Intuitionistic.Unrestricted.Lambda.ToAgda Univ ⟦_⟧ᵁ using (Λ→ΛΠ)
open import Logic.Intuitionistic.Unrestricted.Agda.Environment public
open Translation (Λ→ΛΠ ◇ LL→Λ ◇ LG→LL) public renaming ([_] to [_]ᵀ)


-- * create aliases for polarised types
np np⁻ n n⁻ s s⁻ : Type
np  = el (+ , NP)
np⁻ = el (- , NP)
n   = el (+ , N)
n⁻  = el (- , N)
s   = el (+ , S)
s⁻  = el (- , S)


-- * setup helper functions
im : (Entity → Bool) → ⟦ n ⇐ n ⟧ᵀ
im p₁ (k , p₂) = k (λ x → p₂ x ∧ p₁ x)

iv : (Entity → Bool) → ⟦ np ⇒ s⁻ ⟧ᵀ
iv p (x , k) = k (p x)

tv : (Entity → Entity → Bool) → ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ
tv p ((x , k) , y) = k (p x y)

gq : ((Entity → Bool) → Bool) → (Bool → Bool → Bool) → ⟦ np ⇐ n ⟧ᵀ
gq q _⊙_ (p₁ , p₂) = q (λ x → p₂ x ⊙ p₁ x)


-- * setup lexicon
dutch : ⟦ n ⇐ n ⟧ᵀ
dutch = im DUTCH

english : ⟦ n ⇐ n ⟧ᵀ
english = im ENGLISH

smiles : ⟦ np ⇒ s⁻ ⟧ᵀ
smiles = iv SMILES

left : ⟦ np ⇒ s⁻ ⟧ᵀ
left = iv LEFT

cheats : ⟦ np ⇒ s⁻ ⟧ᵀ
cheats = iv CHEATS

teases : ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ
teases = tv TEASES

loves : ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ
loves = tv LOVES

thinks : ⟦ (np ⇒ s⁻) ⇐ s⁻ ⟧ᵀ
thinks ((x , k) , y) = k (THINKS x (y id))

thinks' : ⟦ (np ⇒ s⁻) ⇐ (◇ s⁻) ⟧ᵀ
thinks' ((x , k) , y) = k (THINKS x (y id))

everyone : ⟦ (np ⇐ n) ⊗ n ⟧ᵀ
everyone = gq forAll _⊃_ , PERSON

someone : ⟦ (np ⇐ n) ⊗ n ⟧ᵀ
someone = gq exists _∧_ , PERSON

everyone1 : ⟦ (₁ np) ¹ ⟧ᵀ
everyone1 p = forAll (λ x → PERSON x ⊃ p x)

someone1 : ⟦ (₁ np) ¹ ⟧ᵀ
someone1 p = exists (λ x → PERSON x ∧ p x)
