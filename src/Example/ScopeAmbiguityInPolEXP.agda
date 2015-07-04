------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- cg --to-agda --system=polexp --lexicon=exp
--    --parse "mary left"
--    --to "λ k → k (LEFT mary)"
--    --parse "everyone loves mary"
--    --to "λ k → forAll (λ x → PERSON x ⊃ k (LOVES x mary))"
--    --parse "mary loves everyone"
--    --to "λ k → forAll (λ x → PERSON x ⊃ k (LOVES mary x))"
--    --parse "everyone loves someone"
--    --to "λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))"
--    --or "λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))"
--    --parse "mary wants everyone to leave"
--    --to "λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEAVES x)))"
--    --or "λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEAVES x)))"
--    --or "λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEAVES x)))"
--    --parse "mary said everyone left"
--    --to "λ k → k (SAID mary (forAll (λ x → PERSON x ⊃ LEAVES x)))"
------------------------------------------------------------------------


open import Data.Colist        using (fromList)
open import Data.Bool          using (Bool; true; false; _∧_; _∨_)
open import Data.Nat           using (ℕ; suc; zero; _≤?_; _*_)
open import Data.Nat.Show      using (show)
open import Data.List
open import Data.String        using (String; _++_)
open import Data.Product       using (_×_; _,_)
open import Data.Vec           using (Vec; _∷_; []; toList)
open import Function           using (id; _$_)
open import IO                 using (IO; run)
open import Reflection         using (Term)
open import Relation.Nullary   using (Dec; yes; no)
open import Example.System.PolEXP


module Example.ScopeAmbiguityInPolEXP where


module mary_left where

  syn : List (EXP · np · ⊗ · np ⇒ s⁻ · ⊢[ s⁻ ])
  syn = findAll (· np · ⊗ · np ⇒ s⁻ · ⊢[ s⁻ ])

  sem : List ⟦ s⁻ ⟧ᵀ
  sem = map (λ syn → [ syn ]ᵀ (mary ∷ left ∷ [])) syn

  exp : List Term
  exp = quoteTerm (λ (k : Bool → Bool) → k (LEAVES mary))
      ∷ []

  assert : Assert (quoteTerm sem sameAs exp)
  assert = _


module everyone_loves_mary where

  syn : List (EXP · ( np ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · np · ) ⊢[ s⁻ ])
  syn = findAll _

  sem : List ⟦ s⁻ ⟧ᵀ
  sem = map (λ syn → [ syn ]ᵀ (everyone ∷ loves ∷ mary ∷ [])) syn

  exp : List Term
  exp = quoteTerm (λ (k : Bool → Bool) → forAll (λ x → PERSON x ⊃ k (LOVES x mary)))
      ∷ []

  assert : Assert (quoteTerm sem sameAs exp)
  assert = _


module mary_loves_everyone where

  syn : List (EXP · np · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( np ⇐ n ) ⊗ n · ) ⊢[ s⁻ ])
  syn = findAll _

  sem : List ⟦ s⁻ ⟧ᵀ
  sem = map (λ syn → [ syn ]ᵀ (mary ∷ loves ∷ everyone ∷ [])) syn

  exp : List Term
  exp = quoteTerm (λ (k : Bool → Bool) → forAll (λ x → PERSON x ⊃ k (LOVES mary x)))
      ∷ []

  assert : Assert (quoteTerm sem sameAs exp)
  assert = _


module someone_loves_everyone where

  syn : List (EXP · ( np ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( np ⇐ n ) ⊗ n · ) ⊢[ s⁻ ])
  syn = findAll _

  sem : List ⟦ s⁻ ⟧ᵀ
  sem = map (λ syn → [ syn ]ᵀ (someone ∷ loves ∷ everyone ∷ [])) syn

  exp : List Term
  exp = quoteTerm (λ (k : Bool → Bool) → forAll (λ x₁ → PERSON x₁ ⊃ exists (λ x₂ → PERSON x₂ ∧ k (LOVES x₂ x₁))))
      ∷ quoteTerm (λ (k : Bool → Bool) → exists (λ x₁ → PERSON x₁ ∧ forAll (λ x₂ → PERSON x₂ ⊃ k (LOVES x₁ x₂))))
      ∷ []

  assert : Assert (quoteTerm sem sameAs exp)
  assert = _


module mary_wants_everyone_to_leave where

  syn : List (EXP · np · ⊗ ( · ( np ⇒ s⁻ ) ⇐ s⁻ · ⊗ ( · ( np ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ inf · ⊗ · inf · ) ) ) ⊢[ s⁻ ])
  syn = findAll _

  sem : List ⟦ s⁻ ⟧ᵀ
  sem = map (λ syn → [ syn ]ᵀ (mary ∷ wants ∷ everyone ∷ to ∷ leave ∷ [])) syn

  exp : List Term
  exp = quoteTerm (λ (k : Bool → Bool) → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEAVES x))))
      ∷ quoteTerm (λ (k : Bool → Bool) → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEAVES x))))
      ∷ quoteTerm (λ (k : Bool → Bool) → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEAVES x))))
      ∷ []

  assert : Assert (quoteTerm sem sameAs exp)
  assert = _


module mary_said_everyone_left where

  syn : List (EXP · np · ⊗ ( · ( np ⇒ s⁻ ) ⇐ ◇ s⁻ · ⊗ ⟨ · ( np ⇐ n ) ⊗ n · ⊗ · np ⇒ s⁻ · ⟩) ⊢[ s⁻ ])
  syn = findAll _

  sem : List ⟦ s⁻ ⟧ᵀ
  sem = map (λ syn → [ syn ]ᵀ (mary ∷ said ∷ everyone ∷ left ∷ [])) syn

  exp : List Term
  exp = quoteTerm (λ (k : Bool → Bool) → k (SAID mary (forAll (λ x → PERSON x ⊃ LEAVES x))))
      ∷ []

  assert : Assert (quoteTerm sem sameAs exp)
  assert = _


proofList : List Proof
proofList = concat
  $ asProof ("mary" ∷ "left" ∷ []) mary_left.syn
  ∷ asProof ("everyone" ∷ "loves" ∷ "mary" ∷ []) everyone_loves_mary.syn
  ∷ asProof ("mary" ∷ "loves" ∷ "everyone" ∷ []) mary_loves_everyone.syn
  ∷ asProof ("someone" ∷ "loves" ∷ "everyone" ∷ []) someone_loves_everyone.syn
  ∷ asProof ("mary" ∷ "wants" ∷ "everyone" ∷ "to" ∷ "leave" ∷ []) mary_wants_everyone_to_leave.syn
  ∷ asProof ("mary" ∷ "said" ∷ "everyone" ∷ "left" ∷ []) mary_said_everyone_left.syn
  ∷ []


main : _
main = run (writeLaTeX proofList)

-- -}
