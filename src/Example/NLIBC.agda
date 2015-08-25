------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Product       using (Σ; _,_)
open import Data.List          using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)


module Example.NLIBC where


open import Example.System.NLIBC public
open import Reflection.Assertion public using (_↦_)


postulate
  _⊃_    : Bool → Bool → Bool
  MARY   : Entity
  JOHN   : Entity
  PERSON : Entity → Bool
  BOOK   : Entity → Bool
  READ   : Entity → Entity → Bool
  LEFT   : Entity → Bool
  LIKES  : Entity → Entity → Bool
  THINKS : Entity → Bool → Bool
  THE    : (Entity → Bool) → Entity
  SAME   : (((Entity → Bool) → Entity → Bool) → Entity → Bool) → Entity → Bool


data Word : Set where
  mary john book left read likes thinks everyone someone the same he : Word


Lex : Word → List⁺ (Σ Type ⟦_⟧ᵗ)
Lex mary     = (np , MARY) ∷ []
Lex john     = (np , JOHN) ∷ []
Lex book     = (n  , BOOK) ∷ []
Lex left     = (iv , LEFT) ∷ []
Lex likes    = (tv , (λ y x → LIKES x y)) ∷ []
Lex read     = (tv , (λ y x → READ x y)) ∷ []
Lex thinks   = (iv ⇐ s , (λ y x → THINKS x y)) ∷ []
Lex everyone = (s ⇦ (np ⇨ s) , (λ p → FORALL (λ x → PERSON x ⊃ p x))) ∷ []
Lex someone  = (s ⇦ (np ⇨ s) , (λ p → EXISTS (λ x → PERSON x ∧ p x))) ∷ []
Lex the      = (np ⇐ n , THE) ∷ []
Lex same     = (n ⇦ (a ⇨ n) , SAME) ∷ ((np ⇨ s) ⇦ (a ⇨ (np ⇨ s)) , SAME) ∷ []
Lex he       = ((np ⇨ s) ⇦ (np ⇨ (np ⇨ s)) , (λ v x → v x x)) ∷ []


open Lexicon (fromLex grammar Lex) public using (✓_; *_; Parse; parse; interpret)


s₁ : interpret (· mary · , · likes · , · john ·)
   ↦ LIKES MARY JOHN
s₁ = _

s₂ : interpret (· john · , · likes · , · everyone ·)
   ↦ FORALL (λ x → PERSON x ⊃ LIKES JOHN x)
s₂ = _

s₃ : interpret (· everyone · , · likes · , · john ·)
   ↦ FORALL (λ x → PERSON x ⊃ LIKES x JOHN)
s₃ = _

s₄ : interpret (· someone · , · likes · , · everyone ·)
   ↦ [ EXISTS (λ y → PERSON y ∧ FORALL (λ x → PERSON x ⊃ LIKES y x))
     , FORALL (λ x → PERSON x ⊃ EXISTS (λ y → PERSON y ∧ LIKES y x))
     ]
s₄ = _

s₆ : interpret (· everyone · ,  · read · , · the · , · same · , · book ·)
   ↦ [ FORALL (λ x → PERSON x ⊃ READ x (THE (SAME (λ f → f BOOK))))
     , FORALL (λ x → PERSON x ⊃ SAME (λ f y → READ y (THE (f BOOK))) x)
     ]
s₆ = _
