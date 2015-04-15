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


open import Example.System.Base


-- * setup atomic formulas
data Univ : Set where
  N  : Univ
  NP : Univ
  S  : Univ

_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)
N  ≟-Univ N  = yes refl
N  ≟-Univ NP = no (λ ())
N  ≟-Univ S  = no (λ ())
NP ≟-Univ N  = no (λ ())
NP ≟-Univ NP = yes refl
NP ≟-Univ S  = no (λ ())
S  ≟-Univ N  = no (λ ())
S  ≟-Univ NP = no (λ ())
S  ≟-Univ S  = yes refl

⟦_⟧ᵁ : Univ → Set
⟦ N  ⟧ᵁ = Entity → Bool
⟦ NP ⟧ᵁ = Entity
⟦ S  ⟧ᵁ = Bool


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
infixr 4 _⊃_

_⊃_ : Bool → Bool → Bool
true  ⊃ true  = true
true  ⊃ false = false
false ⊃ _     = true

im : (Entity → Bool) → ⟦ n ⇐ n ⟧ᵀ
im p₁ (k , p₂) = k (λ x → p₂ x ∧ p₁ x)

iv : (Entity → Bool) → ⟦ np ⇒ s⁻ ⟧ᵀ
iv p (x , k) = k (p x)

tv : (Entity → Entity → Bool) → ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ
tv p ((x , k) , y) = k (p x y)

gq : ((Entity → Bool) → Bool) → (Bool → Bool → Bool) → ⟦ np ⇐ n ⟧ᵀ
gq q _⊙_ (p₁ , p₂) = q (λ x → p₂ x ⊙ p₁ x)


-- * setup lexicon

abstract
  NICE   : Entity → Bool
  NICE _ = true

  OLD      : Entity → Bool
  OLD john = true
  OLD _    = false

  SMILES      : Entity → Bool
  SMILES mary = true
  SMILES john = true
  SMILES _    = false

  LEFT      : Entity → Bool
  LEFT bill = true
  LEFT _    = false

  CHEATS : Entity → Bool
  CHEATS john = true
  CHEATS _    = false

  _TEASES_ : Entity → Entity → Bool
  mary TEASES bill = true
  _    TEASES _    = false

  _LOVES_ : Entity → Entity → Bool
  john LOVES bill = true
  bill LOVES john = true
  mary LOVES john = true
  john LOVES mary = true
  _    LOVES _    = false

  UNICORN   : ⟦ n ⟧ᵀ
  UNICORN _ = false

  PERSON : ⟦ n ⟧ᵀ
  PERSON _ = true

  TEACHER       : ⟦ n ⟧ᵀ
  TEACHER bill  = true
  TEACHER _     = false

postulate
  THINKS : Entity → Bool → Bool

nice : ⟦ n ⇐ n ⟧ᵀ
nice = im NICE

old : ⟦ n ⇐ n ⟧ᵀ
old = im OLD

smiles : ⟦ np ⇒ s⁻ ⟧ᵀ
smiles = iv SMILES

left : ⟦ np ⇒ s⁻ ⟧ᵀ
left = iv LEFT

cheats : ⟦ np ⇒ s⁻ ⟧ᵀ
cheats = iv CHEATS

teases : ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ
teases = tv _TEASES_

loves : ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ
loves = tv _LOVES_

thinks : ⟦ (np ⇒ s⁻) ⇐ s⁻ ⟧ᵀ
thinks ((x , k) , y) = k (THINKS x (y id))

thinks' : ⟦ (np ⇒ s⁻) ⇐ ◇ s⁻ ⟧ᵀ
thinks' ((x , k) , y) = k (THINKS x (y id))

everyone : ⟦ (np ⇐ n) ⊗ n ⟧ᵀ
everyone = gq forAll _⊃_ , PERSON

someone : ⟦ (np ⇐ n) ⊗ n ⟧ᵀ
someone = gq exists _∧_ , PERSON

everyone1 : ⟦ (₁ np) ¹ ⟧ᵀ
everyone1 = forAll

someone1 : ⟦ (₁ np) ¹ ⟧ᵀ
someone1 = exists
