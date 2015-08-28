------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Bool          using (Bool; _∧_)
open import Data.Product       using (Σ; _,_)
open import Data.List          using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)


module Example.NLCPS where


open import Example.System.NLCPS public


postulate
  JOHN    : Entity
  MARY    : Entity
  BILL    : Entity
  DUTCH   : Entity → Bool
  ENGLISH : Entity → Bool
  SMILES  : Entity → Bool
  LEAVES  : Entity → Bool
  CHEATS  : Entity → Bool
  TEASES  : Entity → Entity → Bool
  LOVES   : Entity → Entity → Bool
  FINDS   : Entity → Entity → Bool
  UNICORN : Entity → Bool
  PERSON  : Entity → Bool
  SAID    : Entity → Bool → Bool
  WANTS   : Entity → Bool → Bool


data Word : Set where
  john mary bill unicorn leave to left
    smiles cheats finds loves wants said
      some a every everyone someone
        : Word


private
  im : (Entity → Bool) → ⟦ n ⇐ n ⟧⁺
  im p₁ (k , p₂) = k (λ x → p₂ x ∧ p₁ x)

  v₀ : (Entity → Bool) → ⟦ np ⇒ s ⟧⁺
  v₀ p (x , k) = k (p x)

  v₁ : (Entity → Entity → Bool) → ⟦ (np ⇒ s) ⇐ np ⟧⁺
  v₁ p ((x , k) , y) = k (p x y)

  gq : ((Entity → Bool) → Bool) → (Bool → Bool → Bool) → ⟦ np ⇐ n ⟧⁺
  gq q _⊙_ (p₁ , p₂) = q (λ x → p₂ x ⊙ p₁ x)


Lex : Word → List⁺ (Σ Type ⟦_⟧⁺)
Lex john      = (np , JOHN) ∷ []
Lex mary      = (np , MARY) ∷ []
Lex bill      = (np , BILL) ∷ []
Lex unicorn   = (n , UNICORN) ∷ []
Lex leave     = (inf , LEAVES) ∷ []
Lex to        = ((np ⇒ s) ⇐ inf , λ {((x , k) , p) → k (p x)}) ∷ []
Lex left      = (np ⇒ s , v₀ LEAVES) ∷ []
Lex smiles    = (np ⇒ s , v₀ SMILES) ∷ []
Lex cheats    = (np ⇒ s , v₀ CHEATS) ∷ []
Lex finds     = ((np ⇒ s) ⇐ np , v₁ FINDS) ∷ []
Lex loves     = ((np ⇒ s) ⇐ np , v₁ LOVES) ∷ []
Lex wants     = ((np ⇒ s) ⇐ s , λ {((x , k) , y) → k (WANTS x (y (λ z → z)))}) ∷ []
Lex said      = ((np ⇒ s) ⇐ ◇ s , λ {((x , k) , y) → k (WANTS x (y (λ z → z)))}) ∷ []
Lex a         = (np ⇐ n , gq EXISTS _∧_) ∷ []
Lex some      = (np ⇐ n , gq EXISTS _∧_) ∷ []
Lex every     = (np ⇐ n , gq FORALL _⊃_) ∷ []
Lex everyone  = ((np ⇐ n) ⊗ n , gq FORALL _⊃_ , PERSON) ∷ []
Lex someone   = ((np ⇐ n) ⊗ n , gq EXISTS _∧_ , PERSON) ∷ []


open Lexicon (fromLex grammar Lex) public using (✓_; *_; Parse; parse; interpret)


-- -}
-- -}
-- -}
-- -}
-- -}
