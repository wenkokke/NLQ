------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                              using (id; const)
open import Data.Bool                             using (Bool; true; false; not; _∧_; _∨_)
open import Data.List                             hiding (_++_)
open import Data.Nat                              using (ℕ)
open import Data.Nat.Show                         using (show)
open import Data.Product                          using (_×_; proj₁; _,_)
open import Data.String                           using (String; _++_)
open import Data.Vec                              using (Vec; toList)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Example.System.PolLG where


open import Example.System.Base public


-- * import focused Lambek-Grishin calculus
open import Logic.Translation
open import Logic.Polarity public using (Polarity; +; -)
open import Logic.Polarity.ToLaTeX Atom using (PolarisedAtomToLaTeX) public
open import Logic.ToLaTeX using (module ToLaTeX)
open import Logic.Classical.Ordered.LambekGrishin.FocPol Atom public
open import Logic.Classical.Ordered.LambekGrishin.FocPol.ToLaTeX Atom public
open import Logic.Classical.Ordered.LambekGrishin.FocPol.ProofSearch Atom _≟-Atom_ public
open import Logic.Classical.Ordered.LambekGrishin.FocPol.ToIntuitionisticLinearLambda Atom S using (⟦_⟧ˢ; LG→LL)
open import Logic.Intuitionistic.Linear.Lambda.ToUnrestricted Atom using (LL→Λ)
open import Logic.Intuitionistic.Unrestricted.Lambda.ToAgda Atom ⟦_⟧ᵁ using (Λ→ΛΠ)
open import Logic.Intuitionistic.Unrestricted.Lambda.EquivalentToIndexed Atom using (Un→Ix)
open import Logic.Intuitionistic.Unrestricted.Lambda.Indexed.Base Atom using (Ix→λ)
open import Logic.Intuitionistic.Unrestricted.Lambda.Untyped.Base using (norm)
open import Logic.Intuitionistic.Unrestricted.Lambda.Untyped.ToLaTeX as UT using ()
open import Logic.Intuitionistic.Unrestricted.Agda.Environment public

open Translation (Λ→ΛΠ ◆         LL→Λ ◆ LG→LL) public renaming ([_] to [_]ᵀ)
open Translation (Ix→λ ◆ Un→Ix ◆ LL→Λ ◆ LG→LL) public using () renaming ([_] to LG→λ)

size : Structure + → ℕ
size Γ = length ⟦ Γ ⟧ˢ

toLaTeX : ∀ {J} (f : LG J) → String
toLaTeX {J} = ToLaTeX.toLaTeX (PolarisedLambekGrishinToLaTeX {J} {{AtomToLaTeX}})

toLaTeXTerm : ∀ {Γ B} (xs : Vec String (length ⟦ Γ ⟧ˢ)) (f : LG Γ ⊢[ B ]) → String
toLaTeXTerm xs f = UT.toLaTeXTerm xs (norm (LG→λ f))


-- * create aliases for polarised types
np np⁻ n n⁻ s s⁻ inf inf⁻ : Type
np   = el (+ , NP)
np⁻  = el (- , NP)
n    = el (+ , N)
n⁻   = el (- , N)
s    = el (+ , S)
s⁻   = el (- , S)
inf  = el (+ , INF)
inf⁻ = el (- , INF)

-- * write proofs
asProof : ∀ {Γ} → Vec String (size Γ) → List (LG Γ ⊢[ s⁻ ]) → List Proof
asProof {Γ} ws ps = map
  (λ {(n , p) → proof (basename ++ show n) sentence (toLaTeX p) (toLaTeXTerm ws p)})
  (zip (upTo (length ps)) ps)
  where
    upTo : ℕ → List ℕ
    upTo n = reverse (downFrom n)
    basename : String
    basename = foldr _++_ "_" (intersperse "_" (toList ws))
    sentence : String
    sentence = foldr _++_ "." (intersperse " " (toList ws))


--modifier : LL el N ⇒ el N ∷ [] ⊢ ⟦ n ⇐ n ⟧ᵀ
--modifier = ⇒ᵢ (⊗ₑ ax (⇒ₑ ax (eᴸ₁ (⇒ₑ ax ax))))
--
--verb₀ : LL el NP ⇒ el S ∷ [] ⊢ ⟦ np ⇒ s⁻ ⟧ᵀ
--verb₀ = ⇒ᵢ (⊗ₑ ax (eᴸ₁ (⇒ₑ ax (eᴸ₁ (⇒ₑ ax ax)))))
--
--verb₁ : LL el NP ⇒ el NP ⇒ el S ∷ [] ⊢ ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ
--verb₁ = ⇒ᵢ (⊗ₑ ax (⊗ₑ ax (eᴸ₁ (⇒ₑ ax (eᴸ₂ (⇒ₑ (⇒ₑ ax ax) ax))))))
--
--infinitive : LL el INF ∷ [] ⊢ ⟦ inf ⟧ᵀ
--infinitive = ax
--
--quantifier : LL (el NP ⇒ el S) ⇒ el S ∷ [] ⊢ ⟦ np ⇐ n ⟧ᵀ
--quantifier = ⇒ᵢ (⊗ₑ ax (eᴸ₂ (⇒ₑ ax {!!})))


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

left cheats smiles : ⟦ np ⇒ s⁻ ⟧ᵀ
left   = iv LEAVES
cheats = iv CHEATS
smiles = iv SMILES

leave :  ⟦ inf ⟧ᵀ
leave = LEAVES

to : ⟦ (np ⇒ s⁻) ⇐ inf ⟧ᵀ
to ((x , k) , p) = k (p x)

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
