--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------


open import Level                                 using (zero)
open import Category.Monad                        using (module RawMonad)
open import Data.Bool                             using (Bool; true; false; not; _∧_; _∨_)
open import Data.List                             hiding (_++_; monad)
open import Data.List.NonEmpty                    using (List⁺; _∷_)
open import Data.Nat                              using (ℕ)
open import Data.Nat.Show as ℕ                    using ()
open import Data.Maybe                            using (Maybe; just; nothing; From-just; from-just; monad)
open import Data.Product                          using (Σ; Σ-syntax; _×_; proj₁; proj₂; _,_)
open import Data.String                           using (String; _++_)
open import Data.Traversable                      using (module RawTraversable)
open import Data.Vec                              using (Vec; toList)
open import Function                              using (flip; id; const)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Reflection                            using (Term)


module Example.System.PolLG where

open import Example.System.Base public hiding (module Default)
open import TypeLogicalGrammar
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
open import Logic.Intuitionistic.Unrestricted.Agda.Environment
open import Logic.Intuitionistic.Unrestricted.Agda.ToLaTeX using (show)

open Translation (Λ→ΛΠ ◆         LL→Λ ◆ LG→LL) public renaming ([_] to [_]ᵀ)
open Translation (Ix→λ ◆ Un→Ix ◆ LL→Λ ◆ LG→LL) public using () renaming ([_] to LG→λ)

size : Structure + → ℕ
size Γ = length ⟦ Γ ⟧ˢ

toLaTeX : ∀ {J} (f : LG J) → String
toLaTeX {J} = ToLaTeX.toLaTeX (PolarisedLambekGrishinToLaTeX {J} {{AtomToLaTeX}})

toLaTeXTerm : ∀ {Γ B} (xs : Vec String (length ⟦ Γ ⟧ˢ)) (f : LG Γ ⊢[ B ]) → String
toLaTeXTerm xs f = UT.toLaTeXTerm xs (norm (LG→λ f))


-- * create aliases for polarised types
np n s⁻ inf : Type
np   = el (+ , NP)
n    = el (+ , N)
s⁻   = el (- , S)
inf  = el (+ , INF)


-- * setup helper functions
private
  im : (Entity → Bool) → ⟦ n ⇐ n ⟧ᵀ
  im p₁ (k , p₂) = k (λ x → p₂ x ∧ p₁ x)

  v₀ : (Entity → Bool) → ⟦ np ⇒ s⁻ ⟧ᵀ
  v₀ p (x , k) = k (p x)

  v₁ : (Entity → Entity → Bool) → ⟦ (np ⇒ s⁻) ⇐ np ⟧ᵀ
  v₁ p ((x , k) , y) = k (p x y)

  gq : ((Entity → Bool) → Bool) → (Bool → Bool → Bool) → ⟦ np ⇐ n ⟧ᵀ
  gq q _⊙_ (p₁ , p₂) = q (λ x → p₂ x ⊙ p₁ x)


-- * write proofs

open RawMonad (monad {Level.zero}) using (_<$>_; pure; _⊛_)

asProof′ : ∀ {Γ} (ps : List (LG Γ ⊢[ s⁻ ])) (ts : List Term) → Vec String (size Γ) → List Proof
asProof′ {Γ} ps ts ws = map
  (λ x → proof (basename ++ ℕ.show (proj₁ x)) sentence (toLaTeX (proj₁ (proj₂ x))) (show (proj₂ (proj₂ x))))
  (zip (upTo (length ps)) (zip ps ts))
  where
    upTo : ℕ → List ℕ
    upTo n = reverse (downFrom n)
    basename : String
    basename = foldr _++_ "_" (intersperse "_" (toList ws))
    sentence : String
    sentence = foldr _++_ "." (intersperse " " (toList ws))

asProof : ∀ {Γ} (ws : String) (ps : List (LG Γ ⊢[ s⁻ ])) (ts : Term)
        → From-just (List Proof) (asProof′ ps <$> list ts ⊛ ((size Γ) words ws))
asProof {Γ} ws ps ts = from-just (asProof′ ps <$> (list ts) ⊛ ((size Γ) words ws))


-- * Create a module which abstracts over the lexicon.

module Custom (Word : Set) (Lex : Word → List⁺ (Σ[ A ∈ Type ] ⟦ A ⟧ᵀ)) where

  -- * create an instance of type-logical grammar
  typeLogicalGrammar : TypeLogicalGrammar
  typeLogicalGrammar = record
    { Type           = Type
    ; Struct         = Struct
    ; rawTraversable = rawTraversable
    ; _⊢_            = λ X B → LG ⌊ X ⌋ ⊢[ B ]
    ; findAll        = λ X B → findAll (⌊ X ⌋ ⊢[ B ])
    ; s              = s⁻
    ; toAgdaType     = ⟦_⟧ᵀ
    ; toAgdaTerm     = λ X f → [ f ]ᵀ (combine X)
    ; Word           = Word
    ; Lex            = Lex
    }
    where
      ⌊_⌋ : Struct Type → Structure +
      ⌊ · A · ⌋ = ·     A     ·
      ⌊ ⟨ X ⟩ ⌋ = ⟨   ⌊ X ⌋   ⟩
      ⌊ X , Y ⌋ = ⌊ X ⌋ ⊗ ⌊ Y ⌋

      combine : (X : Struct (Σ[ A ∈ Type ] ⟦ A ⟧ᵀ)) → Env _
      combine ·  A  · = proj₂ A ∷ []
      combine ⟨  X  ⟩ = combine X
      combine (X , Y) = append (combine X) (combine Y)

  open TypeLogicalGrammar.TypeLogicalGrammar typeLogicalGrammar public using (✓_; *_; ⟦_⟧; parse)



module Default where

  open Example.System.Base.Default public

  Lex : Word → List⁺ (Σ[ A ∈ Type ] ⟦ A ⟧ᵀ)
  Lex john     = (np , JOHN) ∷ []
  Lex mary     = (np , MARY) ∷ []
  Lex bill     = (np , BILL) ∷ []
  Lex unicorn  = (n , UNICORN) ∷ []
  Lex leave    = (inf , LEAVES) ∷ []
  Lex to       = ((np ⇒ s⁻) ⇐ inf , λ {((x , k) , p) → k (p x)}) ∷ []
  Lex left     = (np ⇒ s⁻ , v₀ LEAVES) ∷ []
  Lex smiles   = (np ⇒ s⁻ , v₀ SMILES) ∷ []
  Lex cheats   = (np ⇒ s⁻ , v₀ CHEATS) ∷ []
  Lex finds    = ((np ⇒ s⁻) ⇐ np , v₁ _FINDS_) ∷ []
  Lex loves    = ((np ⇒ s⁻) ⇐ np , v₁ _LOVES_) ∷ []
  Lex wants    = ((np ⇒ s⁻) ⇐ s⁻ , λ {((x , k) , y) → k (_WANTS_ x (y id))}) ∷ []
  Lex said     = ((np ⇒ s⁻) ⇐ ◇ s⁻ , λ {((x , k) , y) → k (_SAID_ x (y id))}) ∷ []
  Lex a        = (np ⇐ n , gq EXISTS _∧_) ∷ []
  Lex some     = (np ⇐ n , gq EXISTS _∧_) ∷ []
  Lex every    = (np ⇐ n , gq FORALL _⊃_) ∷ []
  Lex everyone = ((np ⇐ n) ⊗ n , gq FORALL _⊃_ , PERSON) ∷ []
  Lex someone  = ((np ⇐ n) ⊗ n , gq EXISTS _∧_ , PERSON) ∷ []

  open Custom Word Lex public
