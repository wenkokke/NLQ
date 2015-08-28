------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Product       using (Σ; _,_)
open import Data.List          using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Reflection         using (type)


module Example.NLIBC where


open import Example.System.NLIBC public


postulate
  MARY                : Entity
  JOHN                : Entity
  SLAUGHTERHOUSE-FIVE : Entity
  BOOK                : Entity → Bool
  PERSON              : Entity → Bool
  AUTHOR              : Entity → Bool
  READ                : Entity → Entity → Bool
  LEFT                : Entity → Bool
  LIKE                : Entity → Entity → Bool
  THINK               : Entity → Bool → Bool
  THE                 : (Entity → Bool) → Entity
  SAME                : (((Entity → Bool) → Entity → Bool) → Entity → Bool) → Entity → Bool
  OF                  : Entity → (Entity → Bool) → Entity → Bool


data Word : Set where
  mary john
    book person author
      read left likes thinks
        a everyone someone
          the same who which of slaughterhouse-five : Word


Lex : Word → List⁺ (Σ Type ⟦_⟧ᵗ)
Lex mary                = (np , MARY) ∷ []
Lex john                = (np , JOHN) ∷ []
Lex slaughterhouse-five = (np , SLAUGHTERHOUSE-FIVE) ∷ []
Lex book                = (n  , BOOK) ∷ []
Lex person              = (n  , PERSON) ∷ []
Lex author              = (n  , AUTHOR) ∷ []
Lex left                = (iv , LEFT) ∷ []
Lex likes               = (tv , (λ y x → LIKE x y)) ∷ []
Lex read                = (tv , (λ y x → READ x y)) ∷ []
Lex thinks              = (iv ⇐ s , (λ y x → THINK x y)) ∷ []
Lex a                   = ((s ⇦ (np ⇨ s)) ⇐ n , (λ p₁ p₂ → EXISTS (λ x → p₁ x ∧ p₂ x))) ∷ []
Lex someone             = (s ⇦ (np ⇨ s) , (λ p → EXISTS (λ x → PERSON x ∧ p x))) ∷ []
Lex everyone            = (s ⇦ (np ⇨ s) , (λ p → FORALL (λ x → PERSON x ⊃ p x))) ∷ []
Lex the                 = (np ⇐ n , THE) ∷ []
Lex same                = (n ⇦ ((n ⇐ n) ⇨ n) , SAME)
                        ∷ ((np ⇨ s) ⇦ ((n ⇐ n) ⇨ (np ⇨ s)) , SAME) ∷ []
Lex who                 = (q ⇐ (np ⇨ s) , (λ p → THE p))
                        ∷ ((n ⇒ n) ⇐ (np ⇨ s) , (λ p₂ p₁ x → p₁ x ∧ p₂ x))
                        ∷ []
Lex which               = (q ⇐ ((np ⇐ n) ⇨ s) , {!!}) ∷ []
Lex of                  = ((n ⇒ n) ⇐ np , (λ y p x → OF x p y)) ∷ []


open Lexicon (fromLex grammar Lex) public using (✓_; *_; Parse_As_; parse_as_; interpret; interpret_as_)


s₁ : interpret · mary · , · likes · , · john · as s
   ↦ LIKE MARY JOHN
s₁ = _

s₂ : interpret · john · , · likes · , · everyone · as s
   ↦ FORALL (λ x → PERSON x ⊃ LIKE JOHN x)
s₂ = _

s₃ : interpret · everyone · , · likes · , · john · as s
   ↦ FORALL (λ x → PERSON x ⊃ LIKE x JOHN)
s₃ = _

s₄ : interpret · someone · , · likes · , · everyone · as s
   ↦ [ EXISTS (λ y → PERSON y ∧ FORALL (λ x → PERSON x ⊃ LIKE y x))
     , FORALL (λ x → PERSON x ⊃ EXISTS (λ y → PERSON y ∧ LIKE y x))
     ]
s₄ = _

s₅ : interpret · who · , · likes · , · mary · as q
   ↦ THE (λ x → LIKE x MARY)
s₅ = _

s₆ : interpret (· a · , · person · , (· who · , · mary · , · likes ·)) , · left · as s
   ↦ EXISTS (λ x → (PERSON x ∧ LIKE MARY x) ∧ LEFT x)
s₆ = _

s₇ : interpret · john · , · likes · , · the · , (· author · , · of · , · slaughterhouse-five ·) as s
   ↦ LIKE JOHN (THE (λ x → OF x AUTHOR SLAUGHTERHOUSE-FIVE))
s₇ = _

--s₈ : interpret · john · , · likes · , · the · , · author · , · of · , · which ·

{-
s₆ : interpret · everyone · ,  · read · , · the · , · same · , · book · as s
   ↦ [ FORALL (λ x → PERSON x ⊃ READ x (THE (SAME (λ f → f BOOK))))
     , FORALL (λ x → PERSON x ⊃ SAME (λ f y → READ y (THE (f BOOK))) x)
     ]
s₆ = _
-}


-- -}
-- -}
-- -}
-- -}
-- -}
