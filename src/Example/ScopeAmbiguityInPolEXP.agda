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


open import Data.Bool using (Bool)
open import Data.List using (List; _∷_; [])
open import Example.System.PolEXP


module Example.ScopeAmbiguityInPolEXP where


example₁
  : ⟦ · mary · , · left · ⟧
  ↦ (λ (k : Bool → Bool) → k (LEAVES MARY))
example₁ = _

example₂
  : ⟦ · everyone · , · loves · , · mary · ⟧
  ↦ (λ (k : Bool → Bool) → FORALL (λ x → PERSON x ⊃ k (x LOVES MARY)))
example₂ = _

example₃
  : ⟦ · mary · , · loves · , · everyone · ⟧
  ↦ (λ (k : Bool → Bool) → FORALL (λ x → PERSON x ⊃ k (MARY LOVES x)))
example₃ = _

example₄
  : ⟦ · someone · , · loves · , · everyone · ⟧
  ↦ (λ (k : Bool → Bool) → FORALL (λ y → PERSON y ⊃ EXISTS (λ x → PERSON x ∧ k (x LOVES y))))
  ∷ (λ (k : Bool → Bool) → EXISTS (λ x → PERSON x ∧ FORALL (λ y → PERSON y ⊃ k (x LOVES y))))
  ∷ []
example₄ = _

example₅
  : ⟦ · mary · , · wants · , · everyone · , · to · , · leave · ⟧
  ↦ (λ (k : Bool → Bool) → FORALL (λ x → PERSON x ⊃ k (MARY WANTS LEAVES x)))
  ∷ (λ (k : Bool → Bool) → k (MARY WANTS FORALL (λ x → PERSON x ⊃ LEAVES x)))
  ∷ []
example₅ = _

example₆
  : ⟦ · mary · , · said · , ⟨ · everyone · , · left · ⟩ ⟧
  ↦ (λ (k : Bool → Bool) → k (MARY SAID FORALL (λ x → PERSON x ⊃ LEAVES x)))
example₆ = _



{-
proofList : List Proof
proofList = concat
  $ asProof "mary left"                    mary_left.syn                    (quoteTerm mary_left.sem)
  ∷ asProof "everyone loves mary"          everyone_loves_mary.syn          (quoteTerm everyone_loves_mary.sem)
  ∷ asProof "mary loves everyone"          mary_loves_everyone.syn          (quoteTerm mary_loves_everyone.sem)
  ∷ asProof "someone loves everyone"       someone_loves_everyone.syn       (quoteTerm someone_loves_everyone.sem)
  ∷ asProof "mary wants everyone to leave" mary_wants_everyone_to_leave.syn (quoteTerm mary_wants_everyone_to_leave.sem)
  ∷ asProof "mary said everyone left"      mary_said_everyone_left.syn      (quoteTerm mary_said_everyone_left.sem)
  ∷ []

main : _
main = run (writeLaTeX proofList)

-- -}
