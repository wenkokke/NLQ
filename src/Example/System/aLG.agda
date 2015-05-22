------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function    using (id; flip)
open import Data.Bool   using (Bool; true; false; not; _∧_; _∨_)
open import Data.String using (String)


module Example.System.aLG where


open import Data.Product        public using (_,_)
open import Example.System.Base public


-- * import focused Lambek-Grishin calculus
open import Logic.Translation
open import Logic.ToLaTeX using (module ToLaTeX)
open import Logic.Classical.Ordered.LambekGrishin.ResMon                              Univ public
open import Logic.Classical.Ordered.LambekGrishin.ResMon.ToLaTeX                      Univ using (LambekGrishinToLaTeX)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.ToIntuitionisticLinearLambda Univ S renaming (CBV′ to RM→LL)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.ToAgda                       Univ Bool ⟦_⟧ᵁ renaming (CBV to RM→ΛΠ)
open import Logic.Intuitionistic.Linear.Lambda.ToUnrestricted                         Univ using (LL→Λ)
open import Logic.Intuitionistic.Unrestricted.Lambda.ToAgda                           Univ ⟦_⟧ᵁ using (Λ→ΛΠ)
open import Logic.Intuitionistic.Unrestricted.Lambda.EquivalentToIndexed              Univ using (Un→Ix)
open import Logic.Intuitionistic.Unrestricted.Lambda.Indexed.ToLaTeX                  Univ public using (toLaTeXTerm)
open import Logic.Intuitionistic.Unrestricted.Agda.Environment
open Translation ( Λ→ΛΠ ◇ LL→Λ ◇ RM→LL) using () renaming (⟦_⟧ᵀ to ⟦_⟧ᵀ′; [_] to [_]ᵀ′)
open Translation (Un→Ix ◇ LL→Λ ◇ RM→LL) public using () renaming ([_] to toTerm)

toLaTeX : ∀ {J} (f : LG J) → String
toLaTeX {J} = ToLaTeX.toLaTeX (LambekGrishinToLaTeX {J} {{UnivToLaTeX}})


-- * create corrected ⟦_⟧ᵀ and [_]ᵀ functions
⟦_⟧ᵀ : Type → Set
⟦ A ⟧ᵀ = (⟦ A ⟧ᵀ′ → Bool) → Bool

[_]ᵀ : ∀ {A B} (f : LG A ⊢ B) → ⟦ A ⟧ᵀ′ → ⟦ B ⟧ᵀ
[ f ]ᵀ e = [ f ]ᵀ′ (e , ∅)


-- * create aliases for types
np n s⁻ : Type
np  = el NP
n   = el N
s⁻  = el S


-- * setup helper functions
im : (Entity → Bool) → ⟦ n ⇐ n ⟧ᵀ′
im f (k , g) = k (λ x → f x ∧ g x)

iv : (Entity → Bool) → ⟦ np ⇒ s⁻ ⟧ᵀ′
iv f (x , k) = k (f x)

tv : (Entity → Entity → Bool) → ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ′
tv p (k , y) = k (λ {(x , k′) → k′ (p x y)})

gq : (Entity → Bool) → ((Entity → Bool) → Bool) → (Bool → Bool → Bool) → ⟦ (np ⇐ n) ⊗ n ⟧ᵀ′
gq p q _⊙_ = (λ {(p₂ , p₁) → q (λ x → p₁ x ⊙ p₂ x)}) , p

gq′ : (Entity → Bool) → ((Entity → Bool) → Bool) → (Bool → Bool → Bool) → ⟦ s⁻ ⇚ (np ⇛ s⁻) ⟧ᵀ′
gq′  p q _⊙_ = λ k → q (λ x → k (p x , λ k → k (λ {(p′ , b) → b ⊙ p′ x})))

-- * setup lexicon
dutch english : ⟦ n ⇐ n ⟧ᵀ′
dutch   = im DUTCH
english = im ENGLISH

left to_leave cheats smiles : ⟦ np ⇒ s⁻ ⟧ᵀ′
left     = iv LEFT
to_leave = iv LEFT
cheats   = iv CHEATS
smiles   = iv SMILES

teases loves : ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ′
teases = tv TEASES
loves  = tv LOVES

wants : ⟦ (np ⇒ s⁻) ⇐ s⁻ ⟧ᵀ′
wants = λ {(k , y) → k (λ {(x , k′) → k′ (WANTS x y)})}

said  : ⟦ (np ⇒ s⁻) ⇐ (◇ s⁻) ⟧ᵀ′
said  = λ {(k , y) → k (λ {(x , k′) → k′ (SAID x y)})}

everyone someone : ⟦ (np ⇐ n) ⊗ n ⟧ᵀ′
everyone = gq PERSON forAll _⊃_
someone  = gq PERSON exists _∧_

everyone′ someone′ : ⟦ s⁻ ⇚ (np ⇛ s⁻) ⟧ᵀ′
everyone′ = gq′ PERSON forAll _⊃_
someone′  = gq′ PERSON exists _∧_
