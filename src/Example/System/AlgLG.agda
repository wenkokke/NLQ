------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function    using (id; flip)
open import Data.Bool   using (Bool; true; false; not; _∧_; _∨_)
open import Data.String using (String)
open import Data.Unit   using (⊤; tt)
open import Data.Vec    using (Vec)


module Example.System.AlgLG where


open import Data.Product        public using (_,_)
open import Example.System.Base public


-- * import focused Lambek-Grishin calculus
open import Logic.Translation
open import Logic.ToLaTeX using (module ToLaTeX)
open import Logic.Classical.Ordered.LambekGrishin.ResMon                 Atom public
open import Logic.Classical.Ordered.LambekGrishin.ResMon.ProofSearch     Atom _≟-Atom_ public
open import Logic.Classical.Ordered.LambekGrishin.ToAgda                 Atom Bool ⟦_⟧ᵁ using (CBV)
open import Logic.Classical.Ordered.LambekGrishin.EquivalentToResMon     Atom public using (Alg→Str↓)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.ToLaTeX         Atom using (LambekGrishinToLaTeX)
open import Logic.Intuitionistic.Unrestricted.Agda.Environment
open Translation (CBV ◇ Alg→Str↓) using () renaming (⟦_⟧ᵀ to ⟦_⟧ᵀ′; [_] to [_]ᵀ′)


toLaTeX : ∀ {J} (f : LG J) → String
toLaTeX {J} f = ToLaTeX.toLaTeX (LambekGrishinToLaTeX {{AtomToLaTeX}}) f


-- * mock definitions for toLaTeXTerm and toTerm which result in the empty string
toLaTeXTerm : ∀ {A B} (xs : Vec String 1) (f : LG A ⊢ B) → String
toLaTeXTerm _ _ = ""


-- * create corrected ⟦_⟧ᵀ and [_]ᵀ functions
⟦_⟧ᵀ : Type → Set
⟦ A ⟧ᵀ = (⟦ A ⟧ᵀ′ → Bool) → Bool

[_]ᵀ : ∀ {A B} (f : LG A ⊢ B) → ⟦ A ⟧ᵀ′ → ⟦ B ⟧ᵀ
[ f ]ᵀ e = [ f ]ᵀ′ e


-- * create aliases for types
np n s⁻ : Type
np  = el NP
n   = el N
s⁻  = el S
inf = el INF

-- * setup helper functions
im : (Entity → Bool) → ⟦ n ⇐ n ⟧ᵀ′
im f = λ k g → k (λ x → f x ∧ g x)

iv : (Entity → Bool) → ⟦ np ⇒ s⁻ ⟧ᵀ′
iv f = λ k x → k (f x)

tv : (Entity → Entity → Bool) → ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ′
tv f = λ k y → k (λ k x → k (f x y))

gq  : (Entity → Bool) → ((Entity → Bool) → Bool) → (Bool → Bool → Bool) → ⟦ (np ⇐ n) ⊗ n ⟧ᵀ′
gq  f q _⊙_ = ((λ g f → q (λ x → f x ⊙ g x)) , f)

-- * setup lexicon
dutch english : ⟦ n ⇐ n ⟧ᵀ′
dutch   = im DUTCH
english = im ENGLISH

left cheats smiles : ⟦ np ⇒ s⁻ ⟧ᵀ′
left     = iv LEAVES
cheats   = iv CHEATS
smiles   = iv SMILES

teases loves : ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ′
teases = tv TEASES
loves  = tv LOVES

leave :  ⟦ inf ⟧ᵀ
leave k = k LEAVES

to : ⟦ (np ⇒ s⁻) ⇐ inf ⟧ᵀ
to k = k (λ k p → k (λ k x → k (p x)))

wants : ⟦ (np ⇒ s⁻) ⇐ s⁻ ⟧ᵀ′
wants = λ k y → k (λ k x → k (WANTS x y))

said  : ⟦ (np ⇒ s⁻) ⇐ (◇ s⁻) ⟧ᵀ′
said  = λ k y → k (λ k x → k (SAID x y))

everyone  someone  : ⟦ (np ⇐ n) ⊗ n ⟧ᵀ′
everyone  = gq PERSON forAll _⊃_
someone   = gq PERSON exists _∧_
