------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (id)
open import Data.Bool
open import Example.System.fLG


module Example.QuantifierRaising where


HE_LEFT₀ : LG · np ⇚ ((np ⇒ s⁻) ⇛ s⁻) · ⊗ · np ⇒ s⁻ · ⊢[ np ⇒ s⁻ ]
HE_LEFT₀ = ⇁ (r⇐⊗ (⇚ᴸ (d⇚⇐ (r⇛⊕ (⇀ (⇛ᴿ (⇁ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻)))) ax⁻))))))

JOHN_LOVES_BILL₀ : LG · np · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · np ·) ⊢[ s⁻ ]
JOHN_LOVES_BILL₀
  = ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))
john_loves_bill₀ : ⟦ s⁻ ⟧ᵀ
john_loves_bill₀ = [ JOHN_LOVES_BILL₀ ]ᵀ (john , loves , bill , ∅)
--> john LOVES bill


JOHN_LOVES_EVERYONE1₀ : LG · np · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (₁ np) ¹ ·) ⊢[ s⁻ ]
JOHN_LOVES_EVERYONE1₀ = ⇁ (r⇒⊗ (r⇒⊗ (¹ᴸ  (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))
john_loves_everyone1₀ : ⟦ s⁻ ⟧ᵀ
john_loves_everyone1₀ = [ JOHN_LOVES_EVERYONE1₀ ]ᵀ (john , loves , everyone1 , ∅)
--> forAll (λ x → john LOVES x)

SOMEONE1_LOVES_MARY₀ : LG · (₁ np) ¹ · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · np ·) ⊢[ s⁻ ]
SOMEONE1_LOVES_MARY₀ = ⇁ (r⇐⊗ (¹ᴸ  (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))
someone1_loves_mary₀ : ⟦ s⁻ ⟧ᵀ
someone1_loves_mary₀ = [ SOMEONE1_LOVES_MARY₀ ]ᵀ (someone1 , loves , mary , ∅)
--> exists (λ x → x LOVES mary)


EVERYONE1_LOVES_SOMEONE1₀ : LG · (₁ np) ¹ · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (₁ np) ¹ ·) ⊢[ s⁻ ]
EVERYONE1_LOVES_SOMEONE1₀ =
  ⇁ (r⇐⊗ (¹ᴸ  (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (¹ᴸ  (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))
everyone1_loves_someone1₀ : ⟦ s⁻ ⟧ᵀ
everyone1_loves_someone1₀ = [ EVERYONE1_LOVES_SOMEONE1₀ ]ᵀ (everyone1 , loves , someone1 , ∅)
--> forAll (λ x → PERSON x ⊃ exists (λ x₁ → PERSON x₁ ∧ x LOVES x₁))

EVERYONE1_LOVES_SOMEONE1₁ : LG · (₁ np) ¹ · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (₁ np) ¹ ·) ⊢[ s⁻ ]
EVERYONE1_LOVES_SOMEONE1₁ =
  ⇁ (r⇒⊗ (r⇒⊗ (¹ᴸ  (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (¹ᴸ  (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))
everyone1_loves_someone1₁ : ⟦ s⁻ ⟧ᵀ
everyone1_loves_someone1₁ = [ EVERYONE1_LOVES_SOMEONE1₁ ]ᵀ (everyone1 , loves , someone1 , ∅)
--> exists (λ x → PERSON x ∧ forAll (λ x₁ → PERSON x₁ ⊃ x₁ LOVES x))

EVERYONE1_LOVES_SOMEONE1₂ : LG · (₁ np) ¹ · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (₁ np) ¹ ·) ⊢[ s⁻ ]
EVERYONE1_LOVES_SOMEONE1₂ =
  ⇁ (r⇐⊗ (¹ᴸ  (r⊗⇐ (r⇒⊗ (r⇒⊗ (¹ᴸ  (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))
everyone1_loves_someone1₂ : ⟦ s⁻ ⟧ᵀ
everyone1_loves_someone1₂ = [ EVERYONE1_LOVES_SOMEONE1₂ ]ᵀ (everyone1 , loves , someone1 , ∅)
--> exists (λ x → PERSON x ∧ forAll (λ x₁ → PERSON x₁ ⊃ x₁ LOVES x))

EVERYONE1_LOVES_SOMEONE1₃ : LG · (₁ np) ¹ · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (₁ np) ¹ ·) ⊢[ s⁻ ]
EVERYONE1_LOVES_SOMEONE1₃ =
  ⇁ (r⇒⊗ (r⇒⊗ (¹ᴸ  (r⊗⇒ (r⊗⇒ (r⇐⊗ (¹ᴸ  (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))
everyone1_loves_someone1₃ : ⟦ s⁻ ⟧ᵀ
everyone1_loves_someone1₃ = [ EVERYONE1_LOVES_SOMEONE1₃ ]ᵀ (everyone1 , loves , someone1 , ∅)
--> forAll (λ x → PERSON x ⊃ exists (λ x₁ → PERSON x₁ ∧ x LOVES x₁))

EVERYONE1_LOVES_SOMEONE1₄ : LG · (₁ np) ¹ · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (₁ np) ¹ ·) ⊢[ s⁻ ]
EVERYONE1_LOVES_SOMEONE1₄ =
  ⇁ (r⇐⊗ (¹ᴸ  (r⊗⇐ (r⇒⊗ (r⇒⊗ (¹ᴸ  (r⊗⇒ (r⊗⇒ (r⇐⊗ (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))
everyone1_loves_someone1₄ : ⟦ s⁻ ⟧ᵀ
everyone1_loves_someone1₄ = [ EVERYONE1_LOVES_SOMEONE1₄ ]ᵀ (everyone1 , loves , someone1 , ∅)
--> forAll (λ x → PERSON x ⊃ exists (λ x₁ → PERSON x₁ ∧ x LOVES x₁))

EVERYONE1_LOVES_SOMEONE1₅ : LG · (₁ np) ¹ · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (₁ np) ¹ ·) ⊢[ s⁻ ]
EVERYONE1_LOVES_SOMEONE1₅ =
  ⇁ (r⇒⊗ (r⇒⊗ (¹ᴸ  (r⊗⇒ (r⊗⇒ (r⇐⊗ (¹ᴸ  (r⊗⇐ (r⇒⊗ (r⇒⊗ (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r₁¹ (⇀ (₁ᴿ  (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))))
everyone1_loves_someone1₅ : ⟦ s⁻ ⟧ᵀ
everyone1_loves_someone1₅ = [ EVERYONE1_LOVES_SOMEONE1₅ ]ᵀ (everyone1 , loves , someone1 , ∅)
--> exists (λ x → PERSON x ∧ forAll (λ x₁ → PERSON x₁ ⊃ x₁ LOVES x))


SOMEONE_LOVES_MARY₀ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · np ·) ⊢[ s⁻ ]
SOMEONE_LOVES_MARY₀ =
  ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ ( ↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))
someone_loves_mary₀ : ⟦ s⁻ ⟧ᵀ
someone_loves_mary₀ = [ SOMEONE_LOVES_MARY₀ ]ᵀ (someone , loves , mary , ∅)
--> exists (λ x → PERSON x ∧ x LOVES mary)

JOHN_LOVES_EVERYONE₀ : LG · np · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
JOHN_LOVES_EVERYONE₀ =
  ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ ( ↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))
john_loves_everyone₀ : ⟦ s⁻ ⟧ᵀ
john_loves_everyone₀ = [ JOHN_LOVES_EVERYONE₀ ]ᵀ (john , loves , everyone , ∅)
--> forAll (λ x → PERSON x ⊃ john LOVES x)


EVERYONE_LOVES_SOMEONE₀ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₀ =
  ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))
everyone_loves_someone₀ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₀ = [ EVERYONE_LOVES_SOMEONE₀ ]ᵀ (everyone , loves , someone , ∅)
--> forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ x LOVES y))

EVERYONE_LOVES_SOMEONE₁ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₁ =
  ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))
everyone_loves_someone₁ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₁ = [ EVERYONE_LOVES_SOMEONE₁ ]ᵀ (everyone , loves , someone , ∅)
--> exists (λ y → PERSON y ∧ forAll (λ y → PERSON x ⊃ x LOVES y))

EVERYONE_LOVES_SOMEONE₂ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₂ =
  ⇁ (r⇐⊗ (⊗ᴸ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))
everyone_loves_someone₂ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₂ = [ EVERYONE_LOVES_SOMEONE₂ ]ᵀ (everyone , loves , someone , ∅)
--> exists (λ y → PERSON y ∧ forAll (λ y → PERSON x ⊃ x LOVES y))

EVERYONE_LOVES_SOMEONE₃ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₃ =
  ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))
everyone_loves_someone₃ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₃ = [ EVERYONE_LOVES_SOMEONE₃ ]ᵀ (everyone , loves , someone , ∅)
--> forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ x LOVES y))

EVERYONE_LOVES_SOMEONE₄ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₄ =
  ⇁ (r⇐⊗ (⊗ᴸ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))
everyone_loves_someone₄ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₄ = [ EVERYONE_LOVES_SOMEONE₄ ]ᵀ (everyone , loves , someone , ∅)
--> forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ x LOVES y))

EVERYONE_LOVES_SOMEONE₅ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₅ =
  ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))))
everyone_loves_someone₅ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₅ = [ EVERYONE_LOVES_SOMEONE₅ ]ᵀ (everyone , loves , someone , ∅)
--> exists (λ y → PERSON y ∧ forAll (λ x → PERSON x ⊃ x LOVES y))
