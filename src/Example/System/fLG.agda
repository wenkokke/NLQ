------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                              using (id; const)
open import Data.Bool                             using (Bool; true; false; not; _∧_; _∨_)
open import Data.List                             using (List; _∷_; []; map; foldr; length)
open import Data.Product                          using (_×_; proj₁; _,_)
open import Data.String                           using (String)
open import Data.Vec                              using (Vec)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Example.System.fLG where


open import Example.System.Base public


-- * import focused Lambek-Grishin calculus
open import Logic.Translation
open import Logic.Polarity public
open import Logic.Polarity.ToLaTeX Atom using (PolarisedAtomToLaTeX) public
open import Logic.ToLaTeX using (module ToLaTeX)
open import Logic.Classical.Ordered.LambekGrishin.FocPol Atom public
open import Logic.Classical.Ordered.LambekGrishin.FocPol.ToLaTeX Atom public
open import Logic.Classical.Ordered.LambekGrishin.FocPol.ToIntuitionisticLinearLambda Atom S using (⟦_⟧ˢ; LG→LL)
open import Logic.Intuitionistic.Linear.Lambda.ToUnrestricted Atom using (LL→Λ)
open import Logic.Intuitionistic.Unrestricted.Lambda.ToAgda Atom ⟦_⟧ᵁ using (Λ→ΛΠ)
open import Logic.Intuitionistic.Unrestricted.Lambda.EquivalentToIndexed Atom using (Un→Ix)
import Logic.Intuitionistic.Unrestricted.Lambda.Indexed.ToLaTeX Atom as ITL
open import Logic.Intuitionistic.Unrestricted.Agda.Environment public

open Translation (Λ→ΛΠ  ◇ LL→Λ ◇ LG→LL) public renaming ([_] to [_]ᵀ)
open Translation (Un→Ix ◇ LL→Λ ◇ LG→LL) public using () renaming ([_] to toTerm)


toLaTeX : ∀ {J} (f : LG J) → String
toLaTeX {J} = ToLaTeX.toLaTeX (PolarisedLambekGrishinToLaTeX {J} {{AtomToLaTeX}})

toLaTeXTerm : ∀ {Γ B} (xs : Vec String (length ⟦ Γ ⟧ˢ)) (f : LG Γ ⊢[ B ]) → String
toLaTeXTerm {Γ} {B} xs f = ITL.toLaTeXTerm xs (toTerm f)


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
dutch english : ⟦ n ⇐ n ⟧ᵀ
dutch   = im DUTCH
english = im ENGLISH

left to_leave cheats smiles : ⟦ np ⇒ s⁻ ⟧ᵀ
left     = iv LEFT
to_leave = iv LEFT
cheats   = iv CHEATS
smiles   = iv SMILES

teases loves : ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ
teases = tv TEASES
loves  = tv LOVES

wants : ⟦ (np ⇒ s⁻) ⇐ s⁻ ⟧ᵀ
wants ((x , k) , y) = k (WANTS x (y id))

said : ⟦ (np ⇒ s⁻) ⇐ (◇ s⁻) ⟧ᵀ
said ((x , k) , y) = k (SAID x (y id))

everyone someone : ⟦ (np ⇐ n) ⊗ n ⟧ᵀ
everyone = gq forAll _⊃_ , PERSON
someone  = gq exists _∧_ , PERSON
