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

open import Data.Colist using (fromList)
open import Data.Bool   using (Bool; true; false; _∧_; _∨_)
open import Data.List   using (List; _∷_; [])
open import Data.String using (String)
open import Data.Vec    using (_∷_; [])
open import Function    using (id)
open import IO          using (IO; mapM′; run)
open import Reflection  using (Term)
open import Example.System.aLG


module Example.ScopeAmbiguityInAlgEXP where


MARY_SAID_EVERYONE_LEFT₀ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ ◇ s⁻ ) ⊗ ◇ ( ( ( np ⇐ n ) ⊗ n ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_SAID_EVERYONE_LEFT₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (m◇ (r⇒⊗ (m⇒ (r⇐⊗ (m⇐ ax ax)) ax))))))
mary_said_everyone_left₀ : ⟦ s⁻  ⟧ᵀ
mary_said_everyone_left₀
  = [ MARY_SAID_EVERYONE_LEFT₀ ]ᵀ (mary , said , everyone , left)



MARY_SAID_EVERYONE_LEFT₁ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ ◇ s⁻ ) ⊗ ◇ ( ( ( np ⇐ n ) ⊗ n ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_SAID_EVERYONE_LEFT₁
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (m◇ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax)))))))
mary_said_everyone_left₁ : ⟦ s⁻  ⟧ᵀ
mary_said_everyone_left₁
  = [ MARY_SAID_EVERYONE_LEFT₁ ]ᵀ (mary , said , everyone , left)
