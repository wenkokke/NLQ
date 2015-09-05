------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function           using (flip; _$_)
open import Data.Product       using (Σ; _,_)
open import Data.List          using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Reflection         using (type)


module Example.NLIBC where


open import Example.System.NLIBC public


postulate
  MARY                : Entity
  JOHN                : Entity
  SPEAKER             : Entity
  SLAUGHTERHOUSE-FIVE : Entity
  BOOK                : Entity → Bool
  PERSON              : Entity → Bool
  AUTHOR              : Entity → Bool
  READ                : Entity → Entity → Bool
  LEFT                : Entity → Bool
  LIKE                : Entity → Entity → Bool
  KNOW                : Entity → Entity → Bool
  THINK               : Entity → Bool → Bool
  THE                 : (Entity → Bool) → Entity
  SAME                : (((Entity → Bool) → Entity → Bool) → Entity → Bool) → Entity → Bool
  OF                  : Entity → (Entity → Bool) → Entity → Bool
  _WITH-APPOSITIVE_   : Entity → Bool → Entity


data Word : Set where
  I mary john
    book person author like know
      read left likes thinks
        a everyone someone
          the same who which of slaughterhouse-five : Word


Lex : Word → List⁺ (Σ Type ⟦_⟧ᵗ)
Lex I                   = (np , SPEAKER) ∷ []
Lex mary                = (np , MARY) ∷ []
Lex john                = (np , JOHN) ∷ []
Lex slaughterhouse-five = (np , SLAUGHTERHOUSE-FIVE) ∷ []
Lex book                = (n  , BOOK) ∷ []
Lex person              = (n  , PERSON) ∷ []
Lex author              = (n  , AUTHOR) ∷ []
Lex left                = (iv , LEFT) ∷ []
Lex know                = (tv , (λ y x → KNOW x y)) ∷ []
Lex like                = (tv , (λ y x → LIKE x y)) ∷ []
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
Lex which               = ((np ⇒ np) ⇐ (np ⇨ s) ⇦ (np ⇨ np)
                        , (λ f p x → x WITH-APPOSITIVE p (f x))) ∷ []
Lex of                  = ((n ⇒ n) ⇐ np , (λ y p x → OF x p y)) ∷ []


open Lexicon (fromLex grammar Lex) public
     using (✓_; *_; Parse_as_; parse_as_; interpret_as_; interpret; interpretParse)


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


module s₈ where

  -- The idea behind this module is as follows: searching with the
  -- full rule ⇨Lλ is beyond the capabilities of Agda, as the search
  -- space gets too big. Therefore, we have implemented the following
  -- proof (syn) manually.
  -- Afterwards, we have used a proof search algorithm we implemented
  -- in Haskell to find the remaining proofs.
  -- The last line of this module checks if the semantics given to our
  -- manually found proof are identical to the remaining proofs.

  phr : Struct Word
  phr = · I · , · read ·
    , ( · a · , · book ·)
    , ( · the · , · author · , · of · , · which ·)
    , ( · I · , · know · )

  syn : Parse phr as s
  syn =         ⇐L  (_ ∙> (_ ∙> ([] <∙ _))) ax                 -- combine `a book'
       $ flip ( ⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _)))) ax             -- QR `a_book' up
       $        ⇨Rλ (_ ∙> (_ ∙> ([] <∙ _)))                    -- QR `a_book' down
       $ flip ( ⇐L  (_ ∙> [])) (⇒L [] ax ax)                   -- combine `I read NP'
       $        ⇦Lλ (_ ∙> ([] <∙ _)) (_ ∙> (_ ∙> (_ ∙> [])))   -- QR `which' up
              ( ⇨Rλ (_ ∙> (_ ∙> (_ ∙> [])))                    -- QR `which' down
              $ ⇐L  (_ ∙> _ ∙> []) ax                          -- combine `of which'
              $ ⇒L  (_ ∙> []) ax                               -- combine `author ow'
              $ ⇐L  [] ax ax                                   -- combine `the aow'
              )
       $ flip (⇐L   (_ ∙> [])) (⇒L [] ax ax)                  -- insert `a_book' into `taow'
       $       ⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax)) -- insert `abtoaw' into `I know'

  sem : ⟦ s ⟧ᵗ
  sem = interpretParse {phr} syn

  syn1  syn2  syn3  syn4  syn5  syn6  syn7  syn8  syn9  syn10 syn11 syn12 syn13 syn14 syn15 : Parse phr as s
  syn16 syn17 syn18 syn19 syn20 syn21 syn22 syn23 syn24 syn25 syn26 syn27 syn28 syn29 syn30 : Parse phr as s
  syn31 syn32 syn33 syn34 syn35 syn36 syn37 syn38 syn39 syn40 syn41 syn42 syn43 syn44 syn45 : Parse phr as s
  syn46 syn47 syn48 syn49 syn50 syn51 syn52 syn53 syn54 syn55 syn56 syn57 syn58 syn59 syn60 : Parse phr as s
  syn61 syn62 syn63 syn64 syn65 syn66 syn67 syn68 syn69 syn70 syn71 syn72 syn73 syn74 syn75 : Parse phr as s

  syn1 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))))) ax))
  syn2 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))))) ax))
  syn3 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax)))) ax))
  syn4 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))))) ax))
  syn5 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))))) ax))
  syn6 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))))) ax))
  syn7 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))))) ax))
  syn8 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax)))) ax))
  syn9 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))))) ax))
  syn10 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))))) ax))
  syn11 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))))) ax))
  syn12 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))))) ax))
  syn13 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax)))) ax))
  syn14 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))))) ax))
  syn15 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))))) ax))
  syn16 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇦Lλ (_ ∙> ([] <∙ _)) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax))) (⇒L [] ax ax))) ax))
  syn17 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇦Lλ (_ ∙> ([] <∙ _)) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax))) (⇒L [] ax ax))) ax))
  syn18 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇦Lλ (_ ∙> ([] <∙ _)) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax))) (⇒L [] ax ax))) ax))
  syn19 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax)))) ax))
  syn20 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))))) ax))
  syn21 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))))) ax))
  syn22 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax)))) ax))
  syn23 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))))) ax))
  syn24 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))))) ax))
  syn25 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax)))) ax))
  syn26 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))))) ax))
  syn27 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))))) ax))
  syn28 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))) ax))))
  syn29 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))) ax))))
  syn30 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn31 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn32 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax))) ax)))
  syn33 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn34 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn35 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))) ax))))
  syn36 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))) ax))))
  syn37 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn38 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn39 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax))) ax)))
  syn40 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn41 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn42 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))) ax))))
  syn43 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))) ax))))
  syn44 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn45 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn46 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax))) ax)))
  syn47 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn48 = (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn49 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))) ax))))
  syn50 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))) ax))))
  syn51 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn52 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn53 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax))) ax)))
  syn54 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn55 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn56 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))) ax))))
  syn57 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L [] (⇐L (_ ∙> []) ax (⇒L [] ax ax)) ax)) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))) ax))))
  syn58 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))) ax))))
  syn59 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))) ax))))
  syn60 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn61 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn62 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax))) ax)))
  syn63 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn64 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn65 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))) ax))))
  syn66 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇐L [] (⇒L [] ax ax) ax))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))) ax))))
  syn67 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))) ax))))
  syn68 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))) ax))))
  syn69 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn70 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn71 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇐L (_ ∙> []) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L [] ax ax)) (⇒L [] ax ax))) ax)))
  syn72 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax)))) ax)))
  syn73 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax))))) ax)))
  syn74 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇐L (_ ∙> []) (⇒L [] ax ax) (⇒L [] ax ax))) ax))))
  syn75 = (⇦Lλ (_ ∙> (_ ∙> (_ ∙> ([] <∙ _)))) (_ ∙> (_ ∙> (_ ∙> []))) (⇨Rλ (_ ∙> (_ ∙> (_ ∙> []))) (⇐L (_ ∙> (_ ∙> [])) ax (⇒L (_ ∙> []) ax (⇐L [] ax ax)))) (⇐L (_ ∙> (_ ∙> (_ ∙> []))) (⇨RgR (_ ∙> []) (⇐L (_ ∙> []) ax (⇒L [] ax ax))) (⇐L (_ ∙> (_ ∙> ([] <∙ _))) ax (⇦Lλ [] (_ ∙> (_ ∙> ([] <∙ _))) (⇨Rλ (_ ∙> (_ ∙> ([] <∙ _))) (⇒L (_ ∙> (_ ∙> [])) ax (⇐L (_ ∙> []) ax (⇒L [] ax ax)))) ax))))

  sem* : List ⟦ s ⟧ᵗ
  sem* = interpretParse {phr} syn1  ∷ interpretParse {phr} syn2  ∷ interpretParse {phr} syn3
       ∷ interpretParse {phr} syn4  ∷ interpretParse {phr} syn5  ∷ interpretParse {phr} syn6
       ∷ interpretParse {phr} syn7  ∷ interpretParse {phr} syn8  ∷ interpretParse {phr} syn9
       ∷ interpretParse {phr} syn10 ∷ interpretParse {phr} syn11 ∷ interpretParse {phr} syn12
       ∷ interpretParse {phr} syn13 ∷ interpretParse {phr} syn14 ∷ interpretParse {phr} syn15
       ∷ interpretParse {phr} syn16 ∷ interpretParse {phr} syn17 ∷ interpretParse {phr} syn18
       ∷ interpretParse {phr} syn19 ∷ interpretParse {phr} syn20 ∷ interpretParse {phr} syn21
       ∷ interpretParse {phr} syn22 ∷ interpretParse {phr} syn23 ∷ interpretParse {phr} syn24
       ∷ interpretParse {phr} syn25 ∷ interpretParse {phr} syn26 ∷ interpretParse {phr} syn27
       ∷ interpretParse {phr} syn28 ∷ interpretParse {phr} syn29 ∷ interpretParse {phr} syn30
       ∷ interpretParse {phr} syn31 ∷ interpretParse {phr} syn32 ∷ interpretParse {phr} syn33
       ∷ interpretParse {phr} syn34 ∷ interpretParse {phr} syn35 ∷ interpretParse {phr} syn36
       ∷ interpretParse {phr} syn37 ∷ interpretParse {phr} syn38 ∷ interpretParse {phr} syn39
       ∷ interpretParse {phr} syn40 ∷ interpretParse {phr} syn41 ∷ interpretParse {phr} syn42
       ∷ interpretParse {phr} syn43 ∷ interpretParse {phr} syn44 ∷ interpretParse {phr} syn45
       ∷ interpretParse {phr} syn46 ∷ interpretParse {phr} syn47 ∷ interpretParse {phr} syn48
       ∷ interpretParse {phr} syn49 ∷ interpretParse {phr} syn50 ∷ interpretParse {phr} syn51
       ∷ interpretParse {phr} syn52 ∷ interpretParse {phr} syn53 ∷ interpretParse {phr} syn54
       ∷ interpretParse {phr} syn55 ∷ interpretParse {phr} syn56 ∷ interpretParse {phr} syn57
       ∷ interpretParse {phr} syn58 ∷ interpretParse {phr} syn59 ∷ interpretParse {phr} syn60
       ∷ interpretParse {phr} syn61 ∷ interpretParse {phr} syn62 ∷ interpretParse {phr} syn63
       ∷ interpretParse {phr} syn64 ∷ interpretParse {phr} syn65 ∷ interpretParse {phr} syn66
       ∷ interpretParse {phr} syn67 ∷ interpretParse {phr} syn68 ∷ interpretParse {phr} syn69
       ∷ interpretParse {phr} syn70 ∷ interpretParse {phr} syn71 ∷ interpretParse {phr} syn72
       ∷ interpretParse {phr} syn73 ∷ interpretParse {phr} syn74 ∷ interpretParse {phr} syn75
       ∷ []

  --check : sem* ↦ sem
  --check = _


--s₉ : interpret · everyone · ,  · read · , · the · , · same · , · book · as s
--   ↦ [ FORALL (λ x → PERSON x ⊃ READ x (THE (SAME (λ f → f BOOK))))
--     , FORALL (λ x → PERSON x ⊃ SAME (λ f y → READ y (THE (f BOOK))) x)
--     ]
--s₉ = _

-- I don't think there's a difference between restrictive and
-- appositive modifiers. I should try this out: interpret np as a set
-- of entities, and n as the same type.  If that works out, then we
-- can analyse both restrictive and appositive modifiers as
-- restrictive functions on sets. Therefore, if I say something about
-- John in an appositive clause which isn't true, then the set empties
-- and we get the same sort of crash that we would expect. Motivating
-- example here is:
--
--   "I read a book the author of which I like."
--
-- Interpreted in the context where I don't know any authors."


-- -}
-- -}
-- -}
-- -}
-- -}
