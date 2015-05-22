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

MARY_LEFT₀ : LG np ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_LEFT₀
  = (r⇒⊗ (m⇒ ax ax))
mary_left₀ : ⟦ s⁻  ⟧ᵀ
mary_left₀
  = [ MARY_LEFT₀ ]ᵀ (mary , left)

LIST_mary_left₀ : List Term
LIST_mary_left₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (LEFT mary)))
  ∷ []
TEST_mary_left₀ : Assert (quoteTerm mary_left₀ ∈ LIST_mary_left₀)
TEST_mary_left₀ = _



EVERYONE_LOVES_MARY₀ : LG ( ( np ⇐ n ) ⊗ n ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ np ) ⊢ s⁻
EVERYONE_LOVES_MARY₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ (r⇐⊗ (m⇐ ax ax)) ax) ax)))
everyone_loves_mary₀ : ⟦ s⁻  ⟧ᵀ
everyone_loves_mary₀
  = [ EVERYONE_LOVES_MARY₀ ]ᵀ (everyone , loves , mary)

LIST_everyone_loves_mary₀ : List Term
LIST_everyone_loves_mary₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES x mary))))
  ∷ []
TEST_everyone_loves_mary₀ : Assert (quoteTerm everyone_loves_mary₀ ∈ LIST_everyone_loves_mary₀)
TEST_everyone_loves_mary₀ = _



EVERYONE_LOVES_MARY₁ : LG ( ( np ⇐ n ) ⊗ n ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ np ) ⊢ s⁻
EVERYONE_LOVES_MARY₁
  = (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))) ax)))
everyone_loves_mary₁ : ⟦ s⁻  ⟧ᵀ
everyone_loves_mary₁
  = [ EVERYONE_LOVES_MARY₁ ]ᵀ (everyone , loves , mary)

LIST_everyone_loves_mary₁ : List Term
LIST_everyone_loves_mary₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES x mary))))
  ∷ []
TEST_everyone_loves_mary₁ : Assert (quoteTerm everyone_loves_mary₁ ∈ LIST_everyone_loves_mary₁)
TEST_everyone_loves_mary₁ = _



EVERYONE_LOVES_MARY₂ : LG ( ( np ⇐ n ) ⊗ n ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ np ) ⊢ s⁻
EVERYONE_LOVES_MARY₂
  = (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax)))) ax)))
everyone_loves_mary₂ : ⟦ s⁻  ⟧ᵀ
everyone_loves_mary₂
  = [ EVERYONE_LOVES_MARY₂ ]ᵀ (everyone , loves , mary)

LIST_everyone_loves_mary₂ : List Term
LIST_everyone_loves_mary₂
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES x mary))))
  ∷ []
TEST_everyone_loves_mary₂ : Assert (quoteTerm everyone_loves_mary₂ ∈ LIST_everyone_loves_mary₂)
TEST_everyone_loves_mary₂ = _



MARY_LOVES_EVERYONE₀ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( ( np ⇐ n ) ⊗ n ) ) ⊢ s⁻
MARY_LOVES_EVERYONE₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (r⇐⊗ (m⇐ ax ax)))))
mary_loves_everyone₀ : ⟦ s⁻  ⟧ᵀ
mary_loves_everyone₀
  = [ MARY_LOVES_EVERYONE₀ ]ᵀ (mary , loves , everyone)

LIST_mary_loves_everyone₀ : List Term
LIST_mary_loves_everyone₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES mary x))))
  ∷ []
TEST_mary_loves_everyone₀ : Assert (quoteTerm mary_loves_everyone₀ ∈ LIST_mary_loves_everyone₀)
TEST_mary_loves_everyone₀ = _



MARY_LOVES_EVERYONE₁ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( ( np ⇐ n ) ⊗ n ) ) ⊢ s⁻
MARY_LOVES_EVERYONE₁
  = (r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) ax))) ax))))
mary_loves_everyone₁ : ⟦ s⁻  ⟧ᵀ
mary_loves_everyone₁
  = [ MARY_LOVES_EVERYONE₁ ]ᵀ (mary , loves , everyone)

LIST_mary_loves_everyone₁ : List Term
LIST_mary_loves_everyone₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES mary x))))
  ∷ []
TEST_mary_loves_everyone₁ : Assert (quoteTerm mary_loves_everyone₁ ∈ LIST_mary_loves_everyone₁)
TEST_mary_loves_everyone₁ = _



EVERYONE_LOVES_SOMEONE₀ : LG ( ( np ⇐ n ) ⊗ n ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( ( np ⇐ n ) ⊗ n ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ (r⇐⊗ (m⇐ ax ax)) ax) (r⇐⊗ (m⇐ ax ax)))))
everyone_loves_someone₀ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₀
  = [ EVERYONE_LOVES_SOMEONE₀ ]ᵀ (everyone , loves , someone)

LIST_everyone_loves_someone₀ : List Term
LIST_everyone_loves_someone₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₀ : Assert (quoteTerm everyone_loves_someone₀ ∈ LIST_everyone_loves_someone₀)
TEST_everyone_loves_someone₀ = _



EVERYONE_LOVES_SOMEONE₁ : LG ( ( np ⇐ n ) ⊗ n ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( ( np ⇐ n ) ⊗ n ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₁
  = (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (r⇐⊗ (m⇐ ax ax)))))) ax)))
everyone_loves_someone₁ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₁
  = [ EVERYONE_LOVES_SOMEONE₁ ]ᵀ (everyone , loves , someone)

LIST_everyone_loves_someone₁ : List Term
LIST_everyone_loves_someone₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₁ : Assert (quoteTerm everyone_loves_someone₁ ∈ LIST_everyone_loves_someone₁)
TEST_everyone_loves_someone₁ = _



EVERYONE_LOVES_SOMEONE₂ : LG ( ( np ⇐ n ) ⊗ n ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( ( np ⇐ n ) ⊗ n ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₂
  = (r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ (r⇐⊗ (m⇐ ax ax)) ax) ax))) ax))))
everyone_loves_someone₂ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₂
  = [ EVERYONE_LOVES_SOMEONE₂ ]ᵀ (everyone , loves , someone)

LIST_everyone_loves_someone₂ : List Term
LIST_everyone_loves_someone₂
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₂ : Assert (quoteTerm everyone_loves_someone₂ ∈ LIST_everyone_loves_someone₂)
TEST_everyone_loves_someone₂ = _



EVERYONE_LOVES_SOMEONE₃ : LG ( ( np ⇐ n ) ⊗ n ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( ( np ⇐ n ) ⊗ n ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₃
  = (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) ax))) ax))))) ax)))
everyone_loves_someone₃ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₃
  = [ EVERYONE_LOVES_SOMEONE₃ ]ᵀ (everyone , loves , someone)

LIST_everyone_loves_someone₃ : List Term
LIST_everyone_loves_someone₃
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₃ : Assert (quoteTerm everyone_loves_someone₃ ∈ LIST_everyone_loves_someone₃)
TEST_everyone_loves_someone₃ = _



EVERYONE_LOVES_SOMEONE₄ : LG ( ( np ⇐ n ) ⊗ n ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( ( np ⇐ n ) ⊗ n ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₄
  = (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax)))) (r⇐⊗ (m⇐ ax ax)))))
everyone_loves_someone₄ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₄
  = [ EVERYONE_LOVES_SOMEONE₄ ]ᵀ (everyone , loves , someone)

LIST_everyone_loves_someone₄ : List Term
LIST_everyone_loves_someone₄
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₄ : Assert (quoteTerm everyone_loves_someone₄ ∈ LIST_everyone_loves_someone₄)
TEST_everyone_loves_someone₄ = _



EVERYONE_LOVES_SOMEONE₅ : LG ( ( np ⇐ n ) ⊗ n ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( ( np ⇐ n ) ⊗ n ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₅
  = (r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax)))) ax))) ax))))
everyone_loves_someone₅ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₅
  = [ EVERYONE_LOVES_SOMEONE₅ ]ᵀ (everyone , loves , someone)

LIST_everyone_loves_someone₅ : List Term
LIST_everyone_loves_someone₅
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₅ : Assert (quoteTerm everyone_loves_someone₅ ∈ LIST_everyone_loves_someone₅)
TEST_everyone_loves_someone₅ = _



EVERYONE_LOVES_SOMEONE₆ : LG ( ( np ⇐ n ) ⊗ n ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( ( np ⇐ n ) ⊗ n ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₆
  = (r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))) ax))))) ax))))
everyone_loves_someone₆ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₆
  = [ EVERYONE_LOVES_SOMEONE₆ ]ᵀ (everyone , loves , someone)

LIST_everyone_loves_someone₆ : List Term
LIST_everyone_loves_someone₆
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₆ : Assert (quoteTerm everyone_loves_someone₆ ∈ LIST_everyone_loves_someone₆)
TEST_everyone_loves_someone₆ = _



MARY_WANTS_EVERYONE_TO_LEAVE₀ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( ( ( np ⇐ n ) ⊗ n ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_WANTS_EVERYONE_TO_LEAVE₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (r⇒⊗ (m⇒ (r⇐⊗ (m⇐ ax ax)) ax)))))
mary_wants_everyone_to_leave₀ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone_to_leave₀
  = [ MARY_WANTS_EVERYONE_TO_LEAVE₀ ]ᵀ (mary , wants , everyone , to_leave)

LIST_mary_wants_everyone_to_leave₀ : List Term
LIST_mary_wants_everyone_to_leave₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone_to_leave₀ : Assert (quoteTerm mary_wants_everyone_to_leave₀ ∈ LIST_mary_wants_everyone_to_leave₀)
TEST_mary_wants_everyone_to_leave₀ = _



MARY_WANTS_EVERYONE_TO_LEAVE₁ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( ( ( np ⇐ n ) ⊗ n ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_WANTS_EVERYONE_TO_LEAVE₁
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax))))))
mary_wants_everyone_to_leave₁ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone_to_leave₁
  = [ MARY_WANTS_EVERYONE_TO_LEAVE₁ ]ᵀ (mary , wants , everyone , to_leave)

LIST_mary_wants_everyone_to_leave₁ : List Term
LIST_mary_wants_everyone_to_leave₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone_to_leave₁ : Assert (quoteTerm mary_wants_everyone_to_leave₁ ∈ LIST_mary_wants_everyone_to_leave₁)
TEST_mary_wants_everyone_to_leave₁ = _



MARY_WANTS_EVERYONE_TO_LEAVE₂ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( ( ( np ⇐ n ) ⊗ n ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_WANTS_EVERYONE_TO_LEAVE₂
  = (r⇒⊗ (r⇒⊗ (r⇒⊗ (m⇒ (r⇐⊗ (m⇐ ax ax)) (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))))))
mary_wants_everyone_to_leave₂ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone_to_leave₂
  = [ MARY_WANTS_EVERYONE_TO_LEAVE₂ ]ᵀ (mary , wants , everyone , to_leave)

LIST_mary_wants_everyone_to_leave₂ : List Term
LIST_mary_wants_everyone_to_leave₂
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone_to_leave₂ : Assert (quoteTerm mary_wants_everyone_to_leave₂ ∈ LIST_mary_wants_everyone_to_leave₂)
TEST_mary_wants_everyone_to_leave₂ = _



MARY_WANTS_EVERYONE_TO_LEAVE₃ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( ( ( np ⇐ n ) ⊗ n ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_WANTS_EVERYONE_TO_LEAVE₃
  = (r⇒⊗ (r⇒⊗ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) (r⇒⊗ (m⇒ ax ax)))))) ax)))))
mary_wants_everyone_to_leave₃ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone_to_leave₃
  = [ MARY_WANTS_EVERYONE_TO_LEAVE₃ ]ᵀ (mary , wants , everyone , to_leave)

LIST_mary_wants_everyone_to_leave₃ : List Term
LIST_mary_wants_everyone_to_leave₃
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone_to_leave₃ : Assert (quoteTerm mary_wants_everyone_to_leave₃ ∈ LIST_mary_wants_everyone_to_leave₃)
TEST_mary_wants_everyone_to_leave₃ = _



MARY_WANTS_EVERYONE_TO_LEAVE₄ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( ( ( np ⇐ n ) ⊗ n ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_WANTS_EVERYONE_TO_LEAVE₄
  = (r⇒⊗ (r⇒⊗ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (m⇒ ax (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))))) ax)))))
mary_wants_everyone_to_leave₄ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone_to_leave₄
  = [ MARY_WANTS_EVERYONE_TO_LEAVE₄ ]ᵀ (mary , wants , everyone , to_leave)

LIST_mary_wants_everyone_to_leave₄ : List Term
LIST_mary_wants_everyone_to_leave₄
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone_to_leave₄ : Assert (quoteTerm mary_wants_everyone_to_leave₄ ∈ LIST_mary_wants_everyone_to_leave₄)
TEST_mary_wants_everyone_to_leave₄ = _



MARY_SAID_EVERYONE_LEFT₀ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ ◇ s⁻ ) ⊗ ◇ ( ( ( np ⇐ n ) ⊗ n ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_SAID_EVERYONE_LEFT₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (m◇ (r⇒⊗ (m⇒ (r⇐⊗ (m⇐ ax ax)) ax))))))
mary_said_everyone_left₀ : ⟦ s⁻  ⟧ᵀ
mary_said_everyone_left₀
  = [ MARY_SAID_EVERYONE_LEFT₀ ]ᵀ (mary , said , everyone , left)

LIST_mary_said_everyone_left₀ : List Term
LIST_mary_said_everyone_left₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (SAID mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_said_everyone_left₀ : Assert (quoteTerm mary_said_everyone_left₀ ∈ LIST_mary_said_everyone_left₀)
TEST_mary_said_everyone_left₀ = _



MARY_SAID_EVERYONE_LEFT₁ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ ◇ s⁻ ) ⊗ ◇ ( ( ( np ⇐ n ) ⊗ n ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_SAID_EVERYONE_LEFT₁
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (m◇ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax)))))))
mary_said_everyone_left₁ : ⟦ s⁻  ⟧ᵀ
mary_said_everyone_left₁
  = [ MARY_SAID_EVERYONE_LEFT₁ ]ᵀ (mary , said , everyone , left)

LIST_mary_said_everyone_left₁ : List Term
LIST_mary_said_everyone_left₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (SAID mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_said_everyone_left₁ : Assert (quoteTerm mary_said_everyone_left₁ ∈ LIST_mary_said_everyone_left₁)
TEST_mary_said_everyone_left₁ = _



EVERYONE′_LOVES_MARY₀ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ np ) ⊢ s⁻
EVERYONE′_LOVES_MARY₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax ax))) ax) ax)))
everyone′_loves_mary₀ : ⟦ s⁻  ⟧ᵀ
everyone′_loves_mary₀
  = [ EVERYONE′_LOVES_MARY₀ ]ᵀ (everyone′ , loves , mary)

LIST_everyone′_loves_mary₀ : List Term
LIST_everyone′_loves_mary₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES x mary))))
  ∷ []
TEST_everyone′_loves_mary₀ : Assert (quoteTerm everyone′_loves_mary₀ ∈ LIST_everyone′_loves_mary₀)
TEST_everyone′_loves_mary₀ = _



EVERYONE′_LOVES_MARY₁ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ np ) ⊢ s⁻
EVERYONE′_LOVES_MARY₁
  = (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))) ax))))
everyone′_loves_mary₁ : ⟦ s⁻  ⟧ᵀ
everyone′_loves_mary₁
  = [ EVERYONE′_LOVES_MARY₁ ]ᵀ (everyone′ , loves , mary)

LIST_everyone′_loves_mary₁ : List Term
LIST_everyone′_loves_mary₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES x mary))))
  ∷ []
TEST_everyone′_loves_mary₁ : Assert (quoteTerm everyone′_loves_mary₁ ∈ LIST_everyone′_loves_mary₁)
TEST_everyone′_loves_mary₁ = _



EVERYONE′_LOVES_MARY₂ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ np ) ⊢ s⁻
EVERYONE′_LOVES_MARY₂
  = (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax))))) ax)))
everyone′_loves_mary₂ : ⟦ s⁻  ⟧ᵀ
everyone′_loves_mary₂
  = [ EVERYONE′_LOVES_MARY₂ ]ᵀ (everyone′ , loves , mary)

LIST_everyone′_loves_mary₂ : List Term
LIST_everyone′_loves_mary₂
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES x mary))))
  ∷ []
TEST_everyone′_loves_mary₂ : Assert (quoteTerm everyone′_loves_mary₂ ∈ LIST_everyone′_loves_mary₂)
TEST_everyone′_loves_mary₂ = _



MARY_LOVES_EVERYONE′₀ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
MARY_LOVES_EVERYONE′₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (r⊕⇚ (r⇛⊕ (m⇛ ax ax))))))
mary_loves_everyone′₀ : ⟦ s⁻  ⟧ᵀ
mary_loves_everyone′₀
  = [ MARY_LOVES_EVERYONE′₀ ]ᵀ (mary , loves , everyone′)

LIST_mary_loves_everyone′₀ : List Term
LIST_mary_loves_everyone′₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES mary x))))
  ∷ []
TEST_mary_loves_everyone′₀ : Assert (quoteTerm mary_loves_everyone′₀ ∈ LIST_mary_loves_everyone′₀)
TEST_mary_loves_everyone′₀ = _



MARY_LOVES_EVERYONE′₁ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
MARY_LOVES_EVERYONE′₁
  = (r⇒⊗ (r⇒⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) ax))) ax)))))
mary_loves_everyone′₁ : ⟦ s⁻  ⟧ᵀ
mary_loves_everyone′₁
  = [ MARY_LOVES_EVERYONE′₁ ]ᵀ (mary , loves , everyone′)

LIST_mary_loves_everyone′₁ : List Term
LIST_mary_loves_everyone′₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES mary x))))
  ∷ []
TEST_mary_loves_everyone′₁ : Assert (quoteTerm mary_loves_everyone′₁ ∈ LIST_mary_loves_everyone′₁)
TEST_mary_loves_everyone′₁ = _



EVERYONE′_LOVES_SOMEONE′₀ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE′_LOVES_SOMEONE′₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax ax))) ax) (r⊕⇚ (r⇛⊕ (m⇛ ax ax))))))
everyone′_loves_someone′₀ : ⟦ s⁻  ⟧ᵀ
everyone′_loves_someone′₀
  = [ EVERYONE′_LOVES_SOMEONE′₀ ]ᵀ (everyone′ , loves , someone′)

LIST_everyone′_loves_someone′₀ : List Term
LIST_everyone′_loves_someone′₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone′_loves_someone′₀ : Assert (quoteTerm everyone′_loves_someone′₀ ∈ LIST_everyone′_loves_someone′₀)
TEST_everyone′_loves_someone′₀ = _



EVERYONE′_LOVES_SOMEONE′₁ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE′_LOVES_SOMEONE′₁
  = (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (r⊕⇚ (r⇛⊕ (m⇛ ax ax))))))) ax))))
everyone′_loves_someone′₁ : ⟦ s⁻  ⟧ᵀ
everyone′_loves_someone′₁
  = [ EVERYONE′_LOVES_SOMEONE′₁ ]ᵀ (everyone′ , loves , someone′)

LIST_everyone′_loves_someone′₁ : List Term
LIST_everyone′_loves_someone′₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone′_loves_someone′₁ : Assert (quoteTerm everyone′_loves_someone′₁ ∈ LIST_everyone′_loves_someone′₁)
TEST_everyone′_loves_someone′₁ = _



EVERYONE′_LOVES_SOMEONE′₂ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE′_LOVES_SOMEONE′₂
  = (r⇒⊗ (r⇒⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax ax))) ax) ax))) ax)))))
everyone′_loves_someone′₂ : ⟦ s⁻  ⟧ᵀ
everyone′_loves_someone′₂
  = [ EVERYONE′_LOVES_SOMEONE′₂ ]ᵀ (everyone′ , loves , someone′)

LIST_everyone′_loves_someone′₂ : List Term
LIST_everyone′_loves_someone′₂
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone′_loves_someone′₂ : Assert (quoteTerm everyone′_loves_someone′₂ ∈ LIST_everyone′_loves_someone′₂)
TEST_everyone′_loves_someone′₂ = _



EVERYONE′_LOVES_SOMEONE′₃ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE′_LOVES_SOMEONE′₃
  = (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) ax))) ax)))))) ax))))
everyone′_loves_someone′₃ : ⟦ s⁻  ⟧ᵀ
everyone′_loves_someone′₃
  = [ EVERYONE′_LOVES_SOMEONE′₃ ]ᵀ (everyone′ , loves , someone′)

LIST_everyone′_loves_someone′₃ : List Term
LIST_everyone′_loves_someone′₃
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone′_loves_someone′₃ : Assert (quoteTerm everyone′_loves_someone′₃ ∈ LIST_everyone′_loves_someone′₃)
TEST_everyone′_loves_someone′₃ = _



EVERYONE′_LOVES_SOMEONE′₄ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE′_LOVES_SOMEONE′₄
  = (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax))))) (r⊕⇚ (r⇛⊕ (m⇛ ax ax))))))
everyone′_loves_someone′₄ : ⟦ s⁻  ⟧ᵀ
everyone′_loves_someone′₄
  = [ EVERYONE′_LOVES_SOMEONE′₄ ]ᵀ (everyone′ , loves , someone′)

LIST_everyone′_loves_someone′₄ : List Term
LIST_everyone′_loves_someone′₄
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone′_loves_someone′₄ : Assert (quoteTerm everyone′_loves_someone′₄ ∈ LIST_everyone′_loves_someone′₄)
TEST_everyone′_loves_someone′₄ = _



EVERYONE′_LOVES_SOMEONE′₅ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE′_LOVES_SOMEONE′₅
  = (r⇒⊗ (r⇒⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇒ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax))))) ax))) ax)))))
everyone′_loves_someone′₅ : ⟦ s⁻  ⟧ᵀ
everyone′_loves_someone′₅
  = [ EVERYONE′_LOVES_SOMEONE′₅ ]ᵀ (everyone′ , loves , someone′)

LIST_everyone′_loves_someone′₅ : List Term
LIST_everyone′_loves_someone′₅
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone′_loves_someone′₅ : Assert (quoteTerm everyone′_loves_someone′₅ ∈ LIST_everyone′_loves_someone′₅)
TEST_everyone′_loves_someone′₅ = _



EVERYONE′_LOVES_SOMEONE′₆ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE′_LOVES_SOMEONE′₆
  = (r⇒⊗ (r⇒⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))) ax)))))) ax)))))
everyone′_loves_someone′₆ : ⟦ s⁻  ⟧ᵀ
everyone′_loves_someone′₆
  = [ EVERYONE′_LOVES_SOMEONE′₆ ]ᵀ (everyone′ , loves , someone′)

LIST_everyone′_loves_someone′₆ : List Term
LIST_everyone′_loves_someone′₆
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone′_loves_someone′₆ : Assert (quoteTerm everyone′_loves_someone′₆ ∈ LIST_everyone′_loves_someone′₆)
TEST_everyone′_loves_someone′₆ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₀ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (r⇒⊗ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax ax))) ax)))))
mary_wants_everyone′_to_leave₀ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₀
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₀ ]ᵀ (mary , wants , everyone′ , to_leave)

LIST_mary_wants_everyone′_to_leave₀ : List Term
LIST_mary_wants_everyone′_to_leave₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₀ : Assert (quoteTerm mary_wants_everyone′_to_leave₀ ∈ LIST_mary_wants_everyone′_to_leave₀)
TEST_mary_wants_everyone′_to_leave₀ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₁ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₁
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax)))))))
mary_wants_everyone′_to_leave₁ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₁
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₁ ]ᵀ (mary , wants , everyone′ , to_leave)

LIST_mary_wants_everyone′_to_leave₁ : List Term
LIST_mary_wants_everyone′_to_leave₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₁ : Assert (quoteTerm mary_wants_everyone′_to_leave₁ ∈ LIST_mary_wants_everyone′_to_leave₁)
TEST_mary_wants_everyone′_to_leave₁ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₂ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₂
  = (r⇒⊗ (r⇒⊗ (r⇒⊗ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax ax))) (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))))))
mary_wants_everyone′_to_leave₂ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₂
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₂ ]ᵀ (mary , wants , everyone′ , to_leave)

LIST_mary_wants_everyone′_to_leave₂ : List Term
LIST_mary_wants_everyone′_to_leave₂
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₂ : Assert (quoteTerm mary_wants_everyone′_to_leave₂ ∈ LIST_mary_wants_everyone′_to_leave₂)
TEST_mary_wants_everyone′_to_leave₂ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₃ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₃
  = (r⇒⊗ (r⇒⊗ (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) (r⇒⊗ (m⇒ ax ax)))))) ax))))))
mary_wants_everyone′_to_leave₃ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₃
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₃ ]ᵀ (mary , wants , everyone′ , to_leave)

LIST_mary_wants_everyone′_to_leave₃ : List Term
LIST_mary_wants_everyone′_to_leave₃
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₃ : Assert (quoteTerm mary_wants_everyone′_to_leave₃ ∈ LIST_mary_wants_everyone′_to_leave₃)
TEST_mary_wants_everyone′_to_leave₃ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₄ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₄
  = (r⇒⊗ (r⇒⊗ (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))))) ax))))))
mary_wants_everyone′_to_leave₄ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₄
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₄ ]ᵀ (mary , wants , everyone′ , to_leave)

LIST_mary_wants_everyone′_to_leave₄ : List Term
LIST_mary_wants_everyone′_to_leave₄
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₄ : Assert (quoteTerm mary_wants_everyone′_to_leave₄ ∈ LIST_mary_wants_everyone′_to_leave₄)
TEST_mary_wants_everyone′_to_leave₄ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₅ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₅
  = (r⇒⊗ (m⇒ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇛⊕ (m⇛ ax (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))))))))) ax))
mary_wants_everyone′_to_leave₅ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₅
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₅ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₅ : List Term
LIST_mary_wants_everyone′_to_leave₅
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₅ : Assert (quoteTerm mary_wants_everyone′_to_leave₅ ∈ LIST_mary_wants_everyone′_to_leave₅)
TEST_mary_wants_everyone′_to_leave₅ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₆ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₆
  = (r⇒⊗ (m⇒ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax (r⇛⊕ (m⇛ ax ax))) ax)))))))) ax))
mary_wants_everyone′_to_leave₆ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₆
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₆ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₆ : List Term
LIST_mary_wants_everyone′_to_leave₆
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₆ : Assert (quoteTerm mary_wants_everyone′_to_leave₆ ∈ LIST_mary_wants_everyone′_to_leave₆)
TEST_mary_wants_everyone′_to_leave₆ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₇ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₇
  = (r⇒⊗ (m⇒ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇐⊗ (m⇐ (r⇚⊕ (d⇚⇒ (r⇛⊕ (m⇛ ax (r⇒⊗ (m⇒ ax ax)))))) ax))))) ax))
mary_wants_everyone′_to_leave₇ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₇
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₇ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₇ : List Term
LIST_mary_wants_everyone′_to_leave₇
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₇ : Assert (quoteTerm mary_wants_everyone′_to_leave₇ ∈ LIST_mary_wants_everyone′_to_leave₇)
TEST_mary_wants_everyone′_to_leave₇ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₈ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₈
  = (r⇒⊗ (m⇒ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇐⊗ (m⇐ (r⇚⊕ (d⇚⇒ (r⇒⊗ (m⇒ ax (r⇛⊕ (m⇛ ax ax)))))) ax))))) ax))
mary_wants_everyone′_to_leave₈ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₈
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₈ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₈ : List Term
LIST_mary_wants_everyone′_to_leave₈
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₈ : Assert (quoteTerm mary_wants_everyone′_to_leave₈ ∈ LIST_mary_wants_everyone′_to_leave₈)
TEST_mary_wants_everyone′_to_leave₈ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₉ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₉
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))))))))))
mary_wants_everyone′_to_leave₉ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₉
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₉ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₉ : List Term
LIST_mary_wants_everyone′_to_leave₉
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₉ : Assert (quoteTerm mary_wants_everyone′_to_leave₉ ∈ LIST_mary_wants_everyone′_to_leave₉)
TEST_mary_wants_everyone′_to_leave₉ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₁₀ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₁₀
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax))) ax)))))))))
mary_wants_everyone′_to_leave₁₀ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₁₀
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₁₀ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₁₀ : List Term
LIST_mary_wants_everyone′_to_leave₁₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₁₀ : Assert (quoteTerm mary_wants_everyone′_to_leave₁₀ ∈ LIST_mary_wants_everyone′_to_leave₁₀)
TEST_mary_wants_everyone′_to_leave₁₀ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₁₁ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₁₁
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇐⊗ (m⇐ (r⇚⊕ (d⇚⇒ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) (r⇒⊗ (m⇒ ax ax)))))) ax))))))
mary_wants_everyone′_to_leave₁₁ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₁₁
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₁₁ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₁₁ : List Term
LIST_mary_wants_everyone′_to_leave₁₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₁₁ : Assert (quoteTerm mary_wants_everyone′_to_leave₁₁ ∈ LIST_mary_wants_everyone′_to_leave₁₁)
TEST_mary_wants_everyone′_to_leave₁₁ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₁₂ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₁₂
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇐⊗ (m⇐ (r⇚⊕ (d⇚⇒ (r⇒⊗ (m⇒ ax (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax)))))) ax))))))
mary_wants_everyone′_to_leave₁₂ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₁₂
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₁₂ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₁₂ : List Term
LIST_mary_wants_everyone′_to_leave₁₂
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₁₂ : Assert (quoteTerm mary_wants_everyone′_to_leave₁₂ ∈ LIST_mary_wants_everyone′_to_leave₁₂)
TEST_mary_wants_everyone′_to_leave₁₂ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₁₃ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₁₃
  = (r⇒⊗ (m⇒ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇛⊕ (m⇛ ax (r⇒⊗ (m⇒ ax ax))))) ax)))))))) ax))
mary_wants_everyone′_to_leave₁₃ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₁₃
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₁₃ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₁₃ : List Term
LIST_mary_wants_everyone′_to_leave₁₃
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₁₃ : Assert (quoteTerm mary_wants_everyone′_to_leave₁₃ ∈ LIST_mary_wants_everyone′_to_leave₁₃)
TEST_mary_wants_everyone′_to_leave₁₃ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₁₄ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₁₄
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇚⊕ (r⊗⇐ (r⇒⊗ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))))) ax))))))))))
mary_wants_everyone′_to_leave₁₄ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₁₄
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₁₄ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₁₄ : List Term
LIST_mary_wants_everyone′_to_leave₁₄
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₁₄ : Assert (quoteTerm mary_wants_everyone′_to_leave₁₄ ∈ LIST_mary_wants_everyone′_to_leave₁₄)
TEST_mary_wants_everyone′_to_leave₁₄ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₁₅ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₁₅
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇚⊕ (r⊗⇐ (r⇒⊗ (m⇒ (r⊕⇚ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax (r⇛⊕ (m⇛ ax ax))) ax)))) ax))))))))))
mary_wants_everyone′_to_leave₁₅ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₁₅
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₁₅ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₁₅ : List Term
LIST_mary_wants_everyone′_to_leave₁₅
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₁₅ : Assert (quoteTerm mary_wants_everyone′_to_leave₁₅ ∈ LIST_mary_wants_everyone′_to_leave₁₅)
TEST_mary_wants_everyone′_to_leave₁₅ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₁₆ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₁₆
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) (r⇒⊗ (m⇒ ax ax))))) ax)))))))))
mary_wants_everyone′_to_leave₁₆ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₁₆
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₁₆ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₁₆ : List Term
LIST_mary_wants_everyone′_to_leave₁₆
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₁₆ : Assert (quoteTerm mary_wants_everyone′_to_leave₁₆ ∈ LIST_mary_wants_everyone′_to_leave₁₆)
TEST_mary_wants_everyone′_to_leave₁₆ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₁₇ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₁₇
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax (r⇚⊕ (r⊗⇐ (r⇒⊗ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax ax))) ax))))) ax)))))))))
mary_wants_everyone′_to_leave₁₇ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₁₇
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₁₇ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₁₇ : List Term
LIST_mary_wants_everyone′_to_leave₁₇
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₁₇ : Assert (quoteTerm mary_wants_everyone′_to_leave₁₇ ∈ LIST_mary_wants_everyone′_to_leave₁₇)
TEST_mary_wants_everyone′_to_leave₁₇ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₁₈ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₁₈
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (r⊗⇒ (r⊗⇐ (r⇒⊗ (m⇒ (r⇒⊗ (d⇚⇒ (r⇛⊕ (m⇛ ax (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) ax))))))) ax)))))))))
mary_wants_everyone′_to_leave₁₈ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₁₈
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₁₈ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₁₈ : List Term
LIST_mary_wants_everyone′_to_leave₁₈
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₁₈ : Assert (quoteTerm mary_wants_everyone′_to_leave₁₈ ∈ LIST_mary_wants_everyone′_to_leave₁₈)
TEST_mary_wants_everyone′_to_leave₁₈ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₁₉ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₁₉
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (r⊗⇒ (r⊗⇐ (r⇒⊗ (m⇒ (r⇒⊗ (d⇚⇒ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax (r⇛⊕ (m⇛ ax ax))) ax))))) ax)))))))))
mary_wants_everyone′_to_leave₁₉ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₁₉
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₁₉ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₁₉ : List Term
LIST_mary_wants_everyone′_to_leave₁₉
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₁₉ : Assert (quoteTerm mary_wants_everyone′_to_leave₁₉ ∈ LIST_mary_wants_everyone′_to_leave₁₉)
TEST_mary_wants_everyone′_to_leave₁₉ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₂₀ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₂₀
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇐⊗ (m⇐ (r⇚⊕ (d⇚⇒ (r⇚⊕ (r⊗⇐ (r⇒⊗ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax (r⇒⊗ (m⇒ ax ax))))) ax)))))) ax))))))
mary_wants_everyone′_to_leave₂₀ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₂₀
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₂₀ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₂₀ : List Term
LIST_mary_wants_everyone′_to_leave₂₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₂₀ : Assert (quoteTerm mary_wants_everyone′_to_leave₂₀ ∈ LIST_mary_wants_everyone′_to_leave₂₀)
TEST_mary_wants_everyone′_to_leave₂₀ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₂₁ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₂₁
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇐⊗ (m⇐ (r⇚⊕ (d⇚⇒ (r⇚⊕ (r⊗⇐ (r⇒⊗ (m⇒ (r⊕⇚ (r⇒⊗ (m⇒ ax (r⇛⊕ (m⇛ ax ax))))) ax)))))) ax))))))
mary_wants_everyone′_to_leave₂₁ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₂₁
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₂₁ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₂₁ : List Term
LIST_mary_wants_everyone′_to_leave₂₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₂₁ : Assert (quoteTerm mary_wants_everyone′_to_leave₂₁ ∈ LIST_mary_wants_everyone′_to_leave₂₁)
TEST_mary_wants_everyone′_to_leave₂₁ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₂₂ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₂₂
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇐⊗ (m⇐ (r⇚⊕ (d⇚⇒ (r⇒⊗ (m⇒ ax (r⇚⊕ (r⊗⇐ (r⇒⊗ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax ax))) ax)))))))) ax))))))
mary_wants_everyone′_to_leave₂₂ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₂₂
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₂₂ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₂₂ : List Term
LIST_mary_wants_everyone′_to_leave₂₂
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₂₂ : Assert (quoteTerm mary_wants_everyone′_to_leave₂₂ ∈ LIST_mary_wants_everyone′_to_leave₂₂)
TEST_mary_wants_everyone′_to_leave₂₂ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₂₃ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₂₃
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇐⊗ (m⇐ (r⇚⊕ (r⊗⇒ (r⊗⇐ (r⇒⊗ (m⇒ (r⇒⊗ (d⇚⇒ (r⇛⊕ (m⇛ ax (r⇒⊗ (m⇒ ax ax)))))) ax))))) ax))))))
mary_wants_everyone′_to_leave₂₃ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₂₃
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₂₃ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₂₃ : List Term
LIST_mary_wants_everyone′_to_leave₂₃
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₂₃ : Assert (quoteTerm mary_wants_everyone′_to_leave₂₃ ∈ LIST_mary_wants_everyone′_to_leave₂₃)
TEST_mary_wants_everyone′_to_leave₂₃ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₂₄ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₂₄
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇐⊗ (m⇐ (r⇚⊕ (r⊗⇒ (r⊗⇐ (r⇒⊗ (m⇒ (r⇒⊗ (d⇚⇒ (r⇒⊗ (m⇒ ax (r⇛⊕ (m⇛ ax ax)))))) ax))))) ax))))))
mary_wants_everyone′_to_leave₂₄ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₂₄
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₂₄ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₂₄ : List Term
LIST_mary_wants_everyone′_to_leave₂₄
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₂₄ : Assert (quoteTerm mary_wants_everyone′_to_leave₂₄ ∈ LIST_mary_wants_everyone′_to_leave₂₄)
TEST_mary_wants_everyone′_to_leave₂₄ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₂₅ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₂₅
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇚⊕ (r⊗⇐ (r⇒⊗ (m⇒ (r⊕⇚ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇛⊕ (m⇛ ax (r⇒⊗ (m⇒ ax ax))))) ax)))) ax))))))))))
mary_wants_everyone′_to_leave₂₅ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₂₅
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₂₅ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₂₅ : List Term
LIST_mary_wants_everyone′_to_leave₂₅
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₂₅ : Assert (quoteTerm mary_wants_everyone′_to_leave₂₅ ∈ LIST_mary_wants_everyone′_to_leave₂₅)
TEST_mary_wants_everyone′_to_leave₂₅ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₂₆ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₂₆
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇚⊕ (r⊗⇐ (r⇒⊗ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax (r⇒⊗ (m⇒ ax ax))))) ax))))) ax)))))))))
mary_wants_everyone′_to_leave₂₆ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₂₆
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₂₆ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₂₆ : List Term
LIST_mary_wants_everyone′_to_leave₂₆
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₂₆ : Assert (quoteTerm mary_wants_everyone′_to_leave₂₆ ∈ LIST_mary_wants_everyone′_to_leave₂₆)
TEST_mary_wants_everyone′_to_leave₂₆ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₂₇ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₂₇
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (d⇚⇒ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇚⊕ (r⊗⇐ (r⇒⊗ (m⇒ (r⊕⇚ (r⇒⊗ (m⇒ ax (r⇛⊕ (m⇛ ax ax))))) ax))))) ax)))))))))
mary_wants_everyone′_to_leave₂₇ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₂₇
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₂₇ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₂₇ : List Term
LIST_mary_wants_everyone′_to_leave₂₇
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₂₇ : Assert (quoteTerm mary_wants_everyone′_to_leave₂₇ ∈ LIST_mary_wants_everyone′_to_leave₂₇)
TEST_mary_wants_everyone′_to_leave₂₇ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₂₈ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₂₈
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (r⊗⇒ (r⊗⇐ (r⇒⊗ (m⇒ (r⇒⊗ (d⇚⇒ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇛⊕ (m⇛ ax (r⇒⊗ (m⇒ ax ax))))) ax))))) ax)))))))))
mary_wants_everyone′_to_leave₂₈ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₂₈
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₂₈ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₂₈ : List Term
LIST_mary_wants_everyone′_to_leave₂₈
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₂₈ : Assert (quoteTerm mary_wants_everyone′_to_leave₂₈ ∈ LIST_mary_wants_everyone′_to_leave₂₈)
TEST_mary_wants_everyone′_to_leave₂₈ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₂₉ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₂₉
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (r⊗⇒ (r⊗⇐ (r⇒⊗ (m⇒ (r⇒⊗ (r⊕⇚ (r⇐⊗ (m⇐ (r⇚⊕ (d⇚⇒ (r⇛⊕ (m⇛ ax (r⇒⊗ (m⇒ ax ax)))))) ax)))) ax)))))))))
mary_wants_everyone′_to_leave₂₉ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₂₉
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₂₉ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₂₉ : List Term
LIST_mary_wants_everyone′_to_leave₂₉
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₂₉ : Assert (quoteTerm mary_wants_everyone′_to_leave₂₉ ∈ LIST_mary_wants_everyone′_to_leave₂₉)
TEST_mary_wants_everyone′_to_leave₂₉ = _



MARY_WANTS_EVERYONE′_TO_LEAVE₃₀ : LG ( np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ s⁻ ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ) ⊗ ( np ⇒ s⁻ ) ⊢ s⁻
MARY_WANTS_EVERYONE′_TO_LEAVE₃₀
  = (r⇐⊗ (r⇒⊗ (r⇒⊗ (d⇚⇒ (r⇚⊕ (r⊗⇒ (r⊗⇐ (r⇒⊗ (m⇒ (r⇒⊗ (r⊕⇚ (r⇐⊗ (m⇐ (r⇚⊕ (d⇚⇒ (r⇒⊗ (m⇒ ax (r⇛⊕ (m⇛ ax ax)))))) ax)))) ax)))))))))
mary_wants_everyone′_to_leave₃₀ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone′_to_leave₃₀
  = [ MARY_WANTS_EVERYONE′_TO_LEAVE₃₀ ]ᵀ ((mary , wants , everyone′) , to_leave)

LIST_mary_wants_everyone′_to_leave₃₀ : List Term
LIST_mary_wants_everyone′_to_leave₃₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone′_to_leave₃₀ : Assert (quoteTerm mary_wants_everyone′_to_leave₃₀ ∈ LIST_mary_wants_everyone′_to_leave₃₀)
TEST_mary_wants_everyone′_to_leave₃₀ = _



MARY_SAID_EVERYONE′_LEFT₀ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ ◇ s⁻ ) ⊗ ◇ ( ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_SAID_EVERYONE′_LEFT₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (m◇ (r⇒⊗ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax ax))) ax))))))
mary_said_everyone′_left₀ : ⟦ s⁻  ⟧ᵀ
mary_said_everyone′_left₀
  = [ MARY_SAID_EVERYONE′_LEFT₀ ]ᵀ (mary , said , everyone′ , left)

LIST_mary_said_everyone′_left₀ : List Term
LIST_mary_said_everyone′_left₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (SAID mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_said_everyone′_left₀ : Assert (quoteTerm mary_said_everyone′_left₀ ∈ LIST_mary_said_everyone′_left₀)
TEST_mary_said_everyone′_left₀ = _



MARY_SAID_EVERYONE′_LEFT₁ : LG np ⊗ ( ( ( np ⇒ s⁻ ) ⇐ ◇ s⁻ ) ⊗ ◇ ( ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( np ⇒ s⁻ ) ) ) ⊢ s⁻
MARY_SAID_EVERYONE′_LEFT₁
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (m◇ (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax))))))))
mary_said_everyone′_left₁ : ⟦ s⁻  ⟧ᵀ
mary_said_everyone′_left₁
  = [ MARY_SAID_EVERYONE′_LEFT₁ ]ᵀ (mary , said , everyone′ , left)

LIST_mary_said_everyone′_left₁ : List Term
LIST_mary_said_everyone′_left₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (SAID mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_said_everyone′_left₁ : Assert (quoteTerm mary_said_everyone′_left₁ ∈ LIST_mary_said_everyone′_left₁)
TEST_mary_said_everyone′_left₁ = _





proofList : List Proof
proofList
  = proof "everyone_loves_mary_0" "Everyone loves mary." (toLaTeX EVERYONE_LOVES_MARY₀) (toLaTeXTerm ("EVERYONE\\_LOVES\\_MARY"  ∷ []) (toTerm EVERYONE_LOVES_MARY₀))
  ∷ proof "everyone_loves_mary_1" "Everyone loves mary." (toLaTeX EVERYONE_LOVES_MARY₁) (toLaTeXTerm ("EVERYONE\\_LOVES\\_MARY"  ∷ []) (toTerm EVERYONE_LOVES_MARY₁))
  ∷ proof "everyone_loves_mary_2" "Everyone loves mary." (toLaTeX EVERYONE_LOVES_MARY₂) (toLaTeXTerm ("EVERYONE\\_LOVES\\_MARY"  ∷ []) (toTerm EVERYONE_LOVES_MARY₂))
  ∷ proof "everyone_loves_someone_0" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₀) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE_LOVES_SOMEONE₀))
  ∷ proof "everyone_loves_someone_1" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₁) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE_LOVES_SOMEONE₁))
  ∷ proof "everyone_loves_someone_2" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₂) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE_LOVES_SOMEONE₂))
  ∷ proof "everyone_loves_someone_3" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₃) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE_LOVES_SOMEONE₃))
  ∷ proof "everyone_loves_someone_4" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₄) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE_LOVES_SOMEONE₄))
  ∷ proof "everyone_loves_someone_5" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₅) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE_LOVES_SOMEONE₅))
  ∷ proof "everyone_loves_someone_6" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₆) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE_LOVES_SOMEONE₆))
  ∷ proof "everyone_loves_mary_0" "Everyone loves mary." (toLaTeX EVERYONE′_LOVES_MARY₀) (toLaTeXTerm ("EVERYONE\\_LOVES\\_MARY"  ∷ []) (toTerm EVERYONE′_LOVES_MARY₀))
  ∷ proof "everyone_loves_mary_1" "Everyone loves mary." (toLaTeX EVERYONE′_LOVES_MARY₁) (toLaTeXTerm ("EVERYONE\\_LOVES\\_MARY"  ∷ []) (toTerm EVERYONE′_LOVES_MARY₁))
  ∷ proof "everyone_loves_mary_2" "Everyone loves mary." (toLaTeX EVERYONE′_LOVES_MARY₂) (toLaTeXTerm ("EVERYONE\\_LOVES\\_MARY"  ∷ []) (toTerm EVERYONE′_LOVES_MARY₂))
  ∷ proof "everyone_loves_someone_0" "Everyone loves someone." (toLaTeX EVERYONE′_LOVES_SOMEONE′₀) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE′_LOVES_SOMEONE′₀))
  ∷ proof "everyone_loves_someone_1" "Everyone loves someone." (toLaTeX EVERYONE′_LOVES_SOMEONE′₁) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE′_LOVES_SOMEONE′₁))
  ∷ proof "everyone_loves_someone_2" "Everyone loves someone." (toLaTeX EVERYONE′_LOVES_SOMEONE′₂) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE′_LOVES_SOMEONE′₂))
  ∷ proof "everyone_loves_someone_3" "Everyone loves someone." (toLaTeX EVERYONE′_LOVES_SOMEONE′₃) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE′_LOVES_SOMEONE′₃))
  ∷ proof "everyone_loves_someone_4" "Everyone loves someone." (toLaTeX EVERYONE′_LOVES_SOMEONE′₄) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE′_LOVES_SOMEONE′₄))
  ∷ proof "everyone_loves_someone_5" "Everyone loves someone." (toLaTeX EVERYONE′_LOVES_SOMEONE′₅) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE′_LOVES_SOMEONE′₅))
  ∷ proof "everyone_loves_someone_6" "Everyone loves someone." (toLaTeX EVERYONE′_LOVES_SOMEONE′₆) (toLaTeXTerm ("EVERYONE\\_LOVES\\_SOMEONE"  ∷ []) (toTerm EVERYONE′_LOVES_SOMEONE′₆))
  ∷ proof "mary_left_0" "Mary left." (toLaTeX MARY_LEFT₀) (toLaTeXTerm ("MARY\\_LEFT"  ∷ []) (toTerm MARY_LEFT₀))
  ∷ proof "mary_loves_everyone_0" "Mary loves everyone." (toLaTeX MARY_LOVES_EVERYONE₀) (toLaTeXTerm ("MARY\\_LOVES\\_EVERYONE"  ∷ []) (toTerm MARY_LOVES_EVERYONE₀))
  ∷ proof "mary_loves_everyone_1" "Mary loves everyone." (toLaTeX MARY_LOVES_EVERYONE₁) (toLaTeXTerm ("MARY\\_LOVES\\_EVERYONE"  ∷ []) (toTerm MARY_LOVES_EVERYONE₁))
  ∷ proof "mary_loves_everyone_0" "Mary loves everyone." (toLaTeX MARY_LOVES_EVERYONE′₀) (toLaTeXTerm ("MARY\\_LOVES\\_EVERYONE"  ∷ []) (toTerm MARY_LOVES_EVERYONE′₀))
  ∷ proof "mary_loves_everyone_1" "Mary loves everyone." (toLaTeX MARY_LOVES_EVERYONE′₁) (toLaTeXTerm ("MARY\\_LOVES\\_EVERYONE"  ∷ []) (toTerm MARY_LOVES_EVERYONE′₁))
  ∷ proof "mary_said_everyone_left_0" "Mary said everyone left." (toLaTeX MARY_SAID_EVERYONE_LEFT₀) (toLaTeXTerm ("MARY\\_SAID\\_EVERYONE\\_LEFT"  ∷ []) (toTerm MARY_SAID_EVERYONE_LEFT₀))
  ∷ proof "mary_said_everyone_left_1" "Mary said everyone left." (toLaTeX MARY_SAID_EVERYONE_LEFT₁) (toLaTeXTerm ("MARY\\_SAID\\_EVERYONE\\_LEFT"  ∷ []) (toTerm MARY_SAID_EVERYONE_LEFT₁))
  ∷ proof "mary_said_everyone_left_0" "Mary said everyone left." (toLaTeX MARY_SAID_EVERYONE′_LEFT₀) (toLaTeXTerm ("MARY\\_SAID\\_EVERYONE\\_LEFT"  ∷ []) (toTerm MARY_SAID_EVERYONE′_LEFT₀))
  ∷ proof "mary_said_everyone_left_1" "Mary said everyone left." (toLaTeX MARY_SAID_EVERYONE′_LEFT₁) (toLaTeXTerm ("MARY\\_SAID\\_EVERYONE\\_LEFT"  ∷ []) (toTerm MARY_SAID_EVERYONE′_LEFT₁))
  ∷ proof "mary_wants_everyone_to_leave_0" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE_TO_LEAVE₀) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE_TO_LEAVE₀))
  ∷ proof "mary_wants_everyone_to_leave_1" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE_TO_LEAVE₁) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE_TO_LEAVE₁))
  ∷ proof "mary_wants_everyone_to_leave_2" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE_TO_LEAVE₂) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE_TO_LEAVE₂))
  ∷ proof "mary_wants_everyone_to_leave_3" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE_TO_LEAVE₃) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE_TO_LEAVE₃))
  ∷ proof "mary_wants_everyone_to_leave_4" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE_TO_LEAVE₄) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE_TO_LEAVE₄))
  ∷ proof "mary_wants_everyone_to_leave_0" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₀) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₀))
  ∷ proof "mary_wants_everyone_to_leave_1" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₁) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₁))
  ∷ proof "mary_wants_everyone_to_leave_2" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₂) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₂))
  ∷ proof "mary_wants_everyone_to_leave_3" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₃) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₃))
  ∷ proof "mary_wants_everyone_to_leave_4" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₄) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₄))
  ∷ proof "mary_wants_everyone_to_leave_5" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₅) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₅))
  ∷ proof "mary_wants_everyone_to_leave_6" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₆) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₆))
  ∷ proof "mary_wants_everyone_to_leave_7" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₇) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₇))
  ∷ proof "mary_wants_everyone_to_leave_8" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₈) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₈))
  ∷ proof "mary_wants_everyone_to_leave_9" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₉) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₉))
  ∷ proof "mary_wants_everyone_to_leave_10" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₁₀) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₁₀))
  ∷ proof "mary_wants_everyone_to_leave_11" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₁₁) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₁₁))
  ∷ proof "mary_wants_everyone_to_leave_12" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₁₂) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₁₂))
  ∷ proof "mary_wants_everyone_to_leave_13" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₁₃) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₁₃))
  ∷ proof "mary_wants_everyone_to_leave_14" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₁₄) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₁₄))
  ∷ proof "mary_wants_everyone_to_leave_15" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₁₅) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₁₅))
  ∷ proof "mary_wants_everyone_to_leave_16" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₁₆) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₁₆))
  ∷ proof "mary_wants_everyone_to_leave_17" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₁₇) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₁₇))
  ∷ proof "mary_wants_everyone_to_leave_18" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₁₈) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₁₈))
  ∷ proof "mary_wants_everyone_to_leave_19" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₁₉) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₁₉))
  ∷ proof "mary_wants_everyone_to_leave_20" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₂₀) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₂₀))
  ∷ proof "mary_wants_everyone_to_leave_21" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₂₁) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₂₁))
  ∷ proof "mary_wants_everyone_to_leave_22" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₂₂) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₂₂))
  ∷ proof "mary_wants_everyone_to_leave_23" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₂₃) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₂₃))
  ∷ proof "mary_wants_everyone_to_leave_24" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₂₄) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₂₄))
  ∷ proof "mary_wants_everyone_to_leave_25" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₂₅) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₂₅))
  ∷ proof "mary_wants_everyone_to_leave_26" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₂₆) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₂₆))
  ∷ proof "mary_wants_everyone_to_leave_27" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₂₇) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₂₇))
  ∷ proof "mary_wants_everyone_to_leave_28" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₂₈) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₂₈))
  ∷ proof "mary_wants_everyone_to_leave_29" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₂₉) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₂₉))
  ∷ proof "mary_wants_everyone_to_leave_30" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE′_TO_LEAVE₃₀) (toLaTeXTerm ("MARY\\_WANTS\\_EVERYONE\\_TO\\_LEAVE"  ∷ []) (toTerm MARY_WANTS_EVERYONE′_TO_LEAVE₃₀))
  ∷ []

main : _
main = run (mapM′ writeProof (fromList proofList))
