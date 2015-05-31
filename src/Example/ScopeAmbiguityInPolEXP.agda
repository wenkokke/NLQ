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
--    --parse "mary wants everyone to_leave"
--    --to "λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))"
--    --or "λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))"
--    --or "λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))"
--    --parse "mary said everyone left"
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
open import Example.System.fLG

module Example.ScopeAmbiguityInPolEXP where



MARY_LEFT₀ : LG · np · ⊗ · np ⇒ s⁻ · ⊢[ s⁻ ]
MARY_LEFT₀
  = (⇁ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻))))
mary_left₀ : ⟦ s⁻  ⟧ᵀ
mary_left₀
  = [ MARY_LEFT₀ ]ᵀ (mary , left , ∅)

LIST_mary_left₀ : List Term
LIST_mary_left₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (LEFT mary)))
  ∷ []
TEST_mary_left₀ : Assert (quoteTerm mary_left₀ ∈ LIST_mary_left₀)
TEST_mary_left₀ = _



EVERYONE_LOVES_MARY₀ : LG · ( np ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · np · ) ⊢[ s⁻ ]
EVERYONE_LOVES_MARY₀
  = (⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))
everyone_loves_mary₀ : ⟦ s⁻  ⟧ᵀ
everyone_loves_mary₀
  = [ EVERYONE_LOVES_MARY₀ ]ᵀ (everyone , loves , mary , ∅)

LIST_everyone_loves_mary₀ : List Term
LIST_everyone_loves_mary₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES x mary))))
  ∷ []
TEST_everyone_loves_mary₀ : Assert (quoteTerm everyone_loves_mary₀ ∈ LIST_everyone_loves_mary₀)
TEST_everyone_loves_mary₀ = _



MARY_LOVES_EVERYONE₀ : LG · np · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( np ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
MARY_LOVES_EVERYONE₀
  = (⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))
mary_loves_everyone₀ : ⟦ s⁻  ⟧ᵀ
mary_loves_everyone₀
  = [ MARY_LOVES_EVERYONE₀ ]ᵀ (mary , loves , everyone , ∅)

LIST_mary_loves_everyone₀ : List Term
LIST_mary_loves_everyone₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (LOVES mary x))))
  ∷ []
TEST_mary_loves_everyone₀ : Assert (quoteTerm mary_loves_everyone₀ ∈ LIST_mary_loves_everyone₀)
TEST_mary_loves_everyone₀ = _



EVERYONE_LOVES_SOMEONE₀ : LG · ( np ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( np ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₀
  = (⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))))))))))
everyone_loves_someone₀ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₀
  = [ EVERYONE_LOVES_SOMEONE₀ ]ᵀ (everyone , loves , someone , ∅)

LIST_everyone_loves_someone₀ : List Term
LIST_everyone_loves_someone₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₀ : Assert (quoteTerm everyone_loves_someone₀ ∈ LIST_everyone_loves_someone₀)
TEST_everyone_loves_someone₀ = _



EVERYONE_LOVES_SOMEONE₁ : LG · ( np ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( np ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₁
  = (⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))))))))))))
everyone_loves_someone₁ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₁
  = [ EVERYONE_LOVES_SOMEONE₁ ]ᵀ (everyone , loves , someone , ∅)

LIST_everyone_loves_someone₁ : List Term
LIST_everyone_loves_someone₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₁ : Assert (quoteTerm everyone_loves_someone₁ ∈ LIST_everyone_loves_someone₁)
TEST_everyone_loves_someone₁ = _



EVERYONE_LOVES_SOMEONE₂ : LG · ( np ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( np ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₂
  = (⇁ (r⇐⊗ (⊗ᴸ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))))))))))))))
everyone_loves_someone₂ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₂
  = [ EVERYONE_LOVES_SOMEONE₂ ]ᵀ (everyone , loves , someone , ∅)

LIST_everyone_loves_someone₂ : List Term
LIST_everyone_loves_someone₂
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₂ : Assert (quoteTerm everyone_loves_someone₂ ∈ LIST_everyone_loves_someone₂)
TEST_everyone_loves_someone₂ = _



EVERYONE_LOVES_SOMEONE₃ : LG · ( np ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( np ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₃
  = (⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))))))))))))))
everyone_loves_someone₃ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₃
  = [ EVERYONE_LOVES_SOMEONE₃ ]ᵀ (everyone , loves , someone , ∅)

LIST_everyone_loves_someone₃ : List Term
LIST_everyone_loves_someone₃
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₃ : Assert (quoteTerm everyone_loves_someone₃ ∈ LIST_everyone_loves_someone₃)
TEST_everyone_loves_someone₃ = _



EVERYONE_LOVES_SOMEONE₄ : LG · ( np ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( np ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₄
  = (⇁ (r⇐⊗ (⊗ᴸ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))))))))))))))))
everyone_loves_someone₄ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₄
  = [ EVERYONE_LOVES_SOMEONE₄ ]ᵀ (everyone , loves , someone , ∅)

LIST_everyone_loves_someone₄ : List Term
LIST_everyone_loves_someone₄
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₄ : Assert (quoteTerm everyone_loves_someone₄ ∈ LIST_everyone_loves_someone₄)
TEST_everyone_loves_someone₄ = _



EVERYONE_LOVES_SOMEONE₅ : LG · ( np ⇐ n ) ⊗ n · ⊗ ( · ( np ⇒ s⁻ ) ⇐ np · ⊗ · ( np ⇐ n ) ⊗ n · ) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₅
  = (⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))))))))))))))))))
everyone_loves_someone₅ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₅
  = [ EVERYONE_LOVES_SOMEONE₅ ]ᵀ (everyone , loves , someone , ∅)

LIST_everyone_loves_someone₅ : List Term
LIST_everyone_loves_someone₅
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ k (LOVES x y)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ k (LOVES y x)))))
  ∷ []
TEST_everyone_loves_someone₅ : Assert (quoteTerm everyone_loves_someone₅ ∈ LIST_everyone_loves_someone₅)
TEST_everyone_loves_someone₅ = _



MARY_WANTS_EVERYONE_TO_LEAVE₀ : LG · np · ⊗ ( · ( np ⇒ s⁻ ) ⇐ s⁻ · ⊗ ( · ( np ⇐ n ) ⊗ n · ⊗ · np ⇒ s⁻ · ) ) ⊢[ s⁻ ]
MARY_WANTS_EVERYONE_TO_LEAVE₀
  = (⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ (⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻))))))))))) (⇒ᴸ ax⁺ ax⁻))))))
mary_wants_everyone_to_leave₀ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone_to_leave₀
  = [ MARY_WANTS_EVERYONE_TO_LEAVE₀ ]ᵀ (mary , wants , everyone , to_leave , ∅)

LIST_mary_wants_everyone_to_leave₀ : List Term
LIST_mary_wants_everyone_to_leave₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone_to_leave₀ : Assert (quoteTerm mary_wants_everyone_to_leave₀ ∈ LIST_mary_wants_everyone_to_leave₀)
TEST_mary_wants_everyone_to_leave₀ = _



MARY_WANTS_EVERYONE_TO_LEAVE₁ : LG · np · ⊗ ( · ( np ⇒ s⁻ ) ⇐ s⁻ · ⊗ ( · ( np ⇐ n ) ⊗ n · ⊗ · np ⇒ s⁻ · ) ) ⊢[ s⁻ ]
MARY_WANTS_EVERYONE_TO_LEAVE₁
  = (⇁ (r⇒⊗ (r⇒⊗ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ (⇁ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻)))) (⇒ᴸ ax⁺ ax⁻)))))))))))))))
mary_wants_everyone_to_leave₁ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone_to_leave₁
  = [ MARY_WANTS_EVERYONE_TO_LEAVE₁ ]ᵀ (mary , wants , everyone , to_leave , ∅)

LIST_mary_wants_everyone_to_leave₁ : List Term
LIST_mary_wants_everyone_to_leave₁
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone_to_leave₁ : Assert (quoteTerm mary_wants_everyone_to_leave₁ ∈ LIST_mary_wants_everyone_to_leave₁)
TEST_mary_wants_everyone_to_leave₁ = _



MARY_WANTS_EVERYONE_TO_LEAVE₂ : LG · np · ⊗ ( · ( np ⇒ s⁻ ) ⇐ s⁻ · ⊗ ( · ( np ⇐ n ) ⊗ n · ⊗ · np ⇒ s⁻ · ) ) ⊢[ s⁻ ]
MARY_WANTS_EVERYONE_TO_LEAVE₂
  = (⇁ (r⇒⊗ (r⇒⊗ (r⇐⊗ (⊗ᴸ (r⊗⇐ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ (⇁ (r⇐⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻)))))))))) (⇒ᴸ ax⁺ ax⁻)))))))))))
mary_wants_everyone_to_leave₂ : ⟦ s⁻  ⟧ᵀ
mary_wants_everyone_to_leave₂
  = [ MARY_WANTS_EVERYONE_TO_LEAVE₂ ]ᵀ (mary , wants , everyone , to_leave , ∅)

LIST_mary_wants_everyone_to_leave₂ : List Term
LIST_mary_wants_everyone_to_leave₂
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → forAll (λ x → PERSON x ⊃ k (WANTS mary (LEFT x)))))
  ∷ quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (WANTS mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_wants_everyone_to_leave₂ : Assert (quoteTerm mary_wants_everyone_to_leave₂ ∈ LIST_mary_wants_everyone_to_leave₂)
TEST_mary_wants_everyone_to_leave₂ = _



MARY_SAID_EVERYONE_LEFT₀ : LG · np · ⊗ ( · ( np ⇒ s⁻ ) ⇐ ◇ s⁻ · ⊗ ⟨ · ( np ⇐ n ) ⊗ n · ⊗ · np ⇒ s⁻ · ⟩) ⊢[ s⁻ ]
MARY_SAID_EVERYONE_LEFT₀
  = (⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ (◇ᴿ (⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻)))))))))))) (⇒ᴸ ax⁺ ax⁻))))))
mary_said_everyone_left₀ : ⟦ s⁻  ⟧ᵀ
mary_said_everyone_left₀
  = [ MARY_SAID_EVERYONE_LEFT₀ ]ᵀ (mary , said , everyone , left , ∅)

LIST_mary_said_everyone_left₀ : List Term
LIST_mary_said_everyone_left₀
  = quoteTerm (id {A = ⟦ s⁻  ⟧ᵀ} (λ k → k (SAID mary (forAll (λ x → PERSON x ⊃ LEFT x)))))
  ∷ []
TEST_mary_said_everyone_left₀ : Assert (quoteTerm mary_said_everyone_left₀ ∈ LIST_mary_said_everyone_left₀)
TEST_mary_said_everyone_left₀ = _



proofList : List Proof
proofList
  = proof "everyone_loves_mary_0" "Everyone loves mary." (toLaTeX EVERYONE_LOVES_MARY₀) (toLaTeXTerm ("everyone"  ∷ "loves"  ∷ "mary"  ∷ []) EVERYONE_LOVES_MARY₀)
  ∷ proof "everyone_loves_someone_0" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₀) (toLaTeXTerm ("everyone"  ∷ "loves"  ∷ "someone"  ∷ []) EVERYONE_LOVES_SOMEONE₀)
  ∷ proof "everyone_loves_someone_1" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₁) (toLaTeXTerm ("everyone"  ∷ "loves"  ∷ "someone"  ∷ []) EVERYONE_LOVES_SOMEONE₁)
  ∷ proof "everyone_loves_someone_2" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₂) (toLaTeXTerm ("everyone"  ∷ "loves"  ∷ "someone"  ∷ []) EVERYONE_LOVES_SOMEONE₂)
  ∷ proof "everyone_loves_someone_3" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₃) (toLaTeXTerm ("everyone"  ∷ "loves"  ∷ "someone"  ∷ []) EVERYONE_LOVES_SOMEONE₃)
  ∷ proof "everyone_loves_someone_4" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₄) (toLaTeXTerm ("everyone"  ∷ "loves"  ∷ "someone"  ∷ []) EVERYONE_LOVES_SOMEONE₄)
  ∷ proof "everyone_loves_someone_5" "Everyone loves someone." (toLaTeX EVERYONE_LOVES_SOMEONE₅) (toLaTeXTerm ("everyone"  ∷ "loves"  ∷ "someone"  ∷ []) EVERYONE_LOVES_SOMEONE₅)
  ∷ proof "mary_left_0" "Mary left." (toLaTeX MARY_LEFT₀) (toLaTeXTerm ("mary"  ∷ "left"  ∷ []) MARY_LEFT₀)
  ∷ proof "mary_loves_everyone_0" "Mary loves everyone." (toLaTeX MARY_LOVES_EVERYONE₀) (toLaTeXTerm ("mary"  ∷ "loves"  ∷ "everyone"  ∷ []) MARY_LOVES_EVERYONE₀)
  ∷ proof "mary_said_everyone_left_0" "Mary said everyone left." (toLaTeX MARY_SAID_EVERYONE_LEFT₀) (toLaTeXTerm ("mary"  ∷ "said"  ∷ "everyone"  ∷ "left"  ∷ []) MARY_SAID_EVERYONE_LEFT₀)
  ∷ proof "mary_wants_everyone_to_leave_0" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE_TO_LEAVE₀) (toLaTeXTerm ("mary"  ∷ "wants"  ∷ "everyone"  ∷ "to\\_leave"  ∷ []) MARY_WANTS_EVERYONE_TO_LEAVE₀)
  ∷ proof "mary_wants_everyone_to_leave_1" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE_TO_LEAVE₁) (toLaTeXTerm ("mary"  ∷ "wants"  ∷ "everyone"  ∷ "to\\_leave"  ∷ []) MARY_WANTS_EVERYONE_TO_LEAVE₁)
  ∷ proof "mary_wants_everyone_to_leave_2" "Mary wants everyone to\\_leave." (toLaTeX MARY_WANTS_EVERYONE_TO_LEAVE₂) (toLaTeXTerm ("mary"  ∷ "wants"  ∷ "everyone"  ∷ "to\\_leave"  ∷ []) MARY_WANTS_EVERYONE_TO_LEAVE₂)
  ∷ []



main : _
main = run (mapM′ writeProof (fromList proofList))
