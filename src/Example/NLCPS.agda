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
  SLAUGHTERHOUSE-FIVE : Entity
  JOHN                : Entity
  MARY                : Entity
  BILL                : Entity
  DUTCH               : Entity → Bool
  ENGLISH             : Entity → Bool
  SMILE               : Entity → Bool
  LEAVE               : Entity → Bool
  CHEAT               : Entity → Bool
  TEASE               : Entity → Entity → Bool
  LIKE                : Entity → Entity → Bool
  LOVE                : Entity → Entity → Bool
  FIND                : Entity → Entity → Bool
  UNICORN             : Entity → Bool
  PERSON              : Entity → Bool
  SAY                 : Entity → Bool → Bool
  WANT                : Entity → Bool → Bool
  AUTHOR              : Entity → Bool
  THE                 : (Entity → Bool) → Entity
  OF                  : Entity → (Entity → Bool) → Entity → Bool
  SPEAKER             : Entity


data Word : Set where
  john mary bill unicorn leave to left
    smiles cheats finds loves likes wants said
      some a every everyone someone
        I like the author of slaughterhouse-five
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
Lex I                   = (np , SPEAKER) ∷ []
Lex slaughterhouse-five = (np , SLAUGHTERHOUSE-FIVE) ∷ []
Lex john                = (np , JOHN) ∷ []
Lex mary                = (np , MARY) ∷ []
Lex bill                = (np , BILL) ∷ []
Lex unicorn             = (n , UNICORN) ∷ []
Lex leave               = (inf , LEAVE) ∷ []
Lex to                  = ((np ⇒ s) ⇐ inf , λ {((x , k) , p) → k (p x)}) ∷ []
Lex left                = (np ⇒ s , v₀ LEAVE) ∷ []
Lex smiles              = (np ⇒ s , v₀ SMILE) ∷ []
Lex cheats              = (np ⇒ s , v₀ CHEAT) ∷ []
Lex finds               = ((np ⇒ s) ⇐ np , v₁ FIND) ∷ []
Lex like                = ((np ⇒ s) ⇐ np , v₁ LIKE) ∷ []
Lex likes               = ((np ⇒ s) ⇐ np , v₁ LIKE) ∷ []
Lex loves               = ((np ⇒ s) ⇐ np , v₁ LOVE) ∷ []
Lex wants               = ((np ⇒ s) ⇐ s , λ {((x , k) , y) → k (WANT x (y (λ z → z)))}) ∷ []
Lex said                = ((np ⇒ s) ⇐ ◇ s , λ {((x , k) , y) → k (WANT x (y (λ z → z)))}) ∷ []
Lex a                   = (np ⇐ n , gq EXISTS _∧_) ∷ []
Lex some                = (np ⇐ n , gq EXISTS _∧_) ∷ []
Lex every               = (np ⇐ n , gq FORALL _⊃_) ∷ []
Lex everyone            = ((np ⇐ n) ⊗ n , gq FORALL _⊃_ , PERSON) ∷ []
Lex someone             = ((np ⇐ n) ⊗ n , gq EXISTS _∧_ , PERSON) ∷ []
Lex the                 = ((np ⇐ n) , (λ {(k , p) → k (THE p)})) ∷ []
Lex author              = (n , AUTHOR) ∷ []
Lex of                  = ((n ⇒ n) ⇐ np , (λ {((p , k) , y) → k (λ x → OF x p y)})) ∷ []


open Lexicon (fromLex grammar Lex) public using (✓_; *_; Parse; parse; interpret)


s₁ : ✓ · I · , · like · , · the · , · author · , · of · , · slaughterhouse-five ·
s₁ = _



-- -}
-- -}
-- -}
-- -}
-- -}
