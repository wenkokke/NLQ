------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Bool          using (Bool; _∧_)
open import Data.Product       using (Σ; _,_)
open import Data.List          using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)


module Example.NL.ResMon where


open import Example.System.NL.ResMon public
open import Reflection.Assertion     public using (_↦_)


postulate
  _⊃_     : Bool → Bool → Bool
  MARY    : Entity
  JOHN    : Entity
  UNICORN : Entity → Bool
  PERSON  : Entity → Bool
  FINDS   : Entity → Entity → Bool
  LIKES   : Entity → Entity → Bool


data Word : Set where
  john
    mary finds a unicorn
    someone likes everyone
      : Word


Lex : Word → List⁺ (Σ Type ⟦_⟧ᵗ)
Lex mary     = (np , MARY) ∷ []
Lex john     = (np , JOHN) ∷ []
Lex a        = (((s ⇐ (np ⇒ s)) ⇐ n)
             , (λ f g → EXISTS (λ x → f x ∧ g x)))
             ∷ (((((np ⇒ s) ⇐ np) ⇒ (np ⇒ s)) ⇐ n)
             , (λ f g x → EXISTS (λ y → f y ∧ g y x)))
             ∷ (((((np ⇒ s) ⇐ np) ⇒ ((s ⇐ (np ⇒ s)) ⇒ s)) ⇐ n)
             , (λ f g p → EXISTS (λ y → f y ∧ p (λ x → g y x))))
             ∷ []
Lex unicorn  = (n  , UNICORN) ∷ []
Lex finds    = (tv , (λ y x → FINDS x y)) ∷ []
Lex someone  = ((s ⇐ (np ⇒ s))
             , (λ g → EXISTS (λ x → PERSON x ∧ g x)))
             ∷ ((((np ⇒ s) ⇐ np) ⇒ (np ⇒ s))
             , (λ g x → EXISTS (λ y → PERSON y ∧ g y x)))
             ∷ (((np ⇒ s) ⇐ np) ⇒ ((s ⇐ (np ⇒ s)) ⇒ s)
             , (λ g p → EXISTS (λ y → PERSON y ∧ p (λ x → g y x))))
             ∷ []
Lex likes    = (tv , (λ y x → LIKES x y)) ∷ []
Lex everyone = ((s ⇐ (np ⇒ s))
             , (λ g → FORALL (λ x → PERSON x ⊃ g x)))
             ∷ ((((np ⇒ s) ⇐ np) ⇒ (np ⇒ s))
             , (λ g x → FORALL (λ y → PERSON y ⊃ g y x)))
             ∷ (((np ⇒ s) ⇐ np) ⇒ ((s ⇐ (np ⇒ s)) ⇒ s)
             , (λ g p → FORALL (λ y → PERSON y ⊃ p (λ x → g y x))))
             ∷ []


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

s₅ : interpret (· mary · , · finds · , · a · , · unicorn ·)
   ↦ EXISTS (λ y → UNICORN y ∧ FINDS MARY y)
s₅ = _

s₆ : interpret ((· a · , · unicorn ·) , · finds · , · mary ·)
   ↦ EXISTS (λ x → UNICORN x ∧ FINDS x MARY)
s₆ = _

s₇ : * · unicorn · , · unicorn · , · unicorn · , · unicorn ·
s₇ = _
