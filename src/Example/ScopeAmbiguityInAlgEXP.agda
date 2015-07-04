------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- cg --to-agda --system=algexp --lexicon=exp
--    --parse "mary left"
--    --to "λ k → k (LEFT mary)"
--    --parse "everyone loves mary"
--    --to "λ k → forAll (λ x → PERSON x ⊃ k (LOVES x mary))"
--    --parse "mary loves everyone"
--    --to "λ k → forAll (λ x → PERSON x ⊃ k (LOVES mary x))"
--    --parse "everyone loves someone"
--    --to "λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))"
--    --or "λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))"
--    --parse "mary wants everyone to_leave"
--    --to "λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))"
--    --or "λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))"
--    --or "λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))"
--    --parse "mary said everyone left"
--    --to "λ k → k (SAID mary (forAll (λ x → PERSON x ⊃ LEFT x)))"
--    --parse "everyone′ loves mary"
--    --to "λ k → forAll (λ x → PERSON x ⊃ k (LOVES x mary))"
--    --parse "mary loves everyone′"
--    --to "λ k → forAll (λ x → PERSON x ⊃ k (LOVES mary x))"
--    --parse "everyone′ loves someone′"
--    --to "λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))"
--    --or "λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))"
--    --parse "mary wants everyone′ to_leave"
--    --to "λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))"
--    --or "λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))"
--    --or "λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))"
--    --parse "mary said everyone′ left"
--    --to "λ k → k (SAID mary (forAll (λ x → PERSON x ⊃ LEFT x)))"
------------------------------------------------------------------------

open import Data.Colist      using (fromList)
open import Data.Bool        using (Bool; true; false; _∧_; _∨_)
open import Data.Nat         using (ℕ; suc; zero; _≤?_; _*_)
open import Data.Nat.Show    using (show)
open import Data.List        using (List; _∷_; []; zip; map)
open import Data.String      using (String; _++_)
open import Data.Product     using (_×_; _,_)
open import Data.Vec         using (_∷_; [])
open import Function         using (id)
open import IO               using (IO; mapM′; run)
open import Reflection       using (Term)
open import Relation.Nullary using (Dec; yes; no)
open import Example.System.AlgLG


module Example.ScopeAmbiguityInAlgEXP where

private
  _^_ : ℕ → ℕ → ℕ
  n ^ zero  = 1
  n ^ suc m = n * (n ^ m)

  {-# TERMINATING #-}
  [_⋯_] : ℕ → ℕ → List ℕ
  [ n ⋯ m ] with m ≤? n
  [ n ⋯ m ] | yes _ = n ∷ []
  [ n ⋯ m ] | no  _ = n ∷ [ suc n ⋯ m ]


synTerms
  = findAll (np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ ◇ s⁻ ) ⊗ ◇ ( ( ( np ⇐ n ) ⊗ n ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻)
semTerms
  = map (λ x → [ x ]ᵀ (mary , said , everyone , left)) synTerms
texTerms
  = map (λ {(n , x) →
           proof
             ("mary_said_everyone_left" ++ show n)
             "Mary said everyone left."
             (toLaTeX x)
             ""
        })
        (zip [ 0 ⋯ 10 ] synTerms)

main : _
main = run (mapM′ writeProof (fromList texTerms))
