------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Example.System.fLG


module Example.QuantifierRaising where


JOHN_LOVES_BILL₀ : LG · np · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · np ·) ⊢[ s⁻ ]
JOHN_LOVES_BILL₀
  = ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))
john_loves_bill₀ : ⟦ s⁻ ⟧ᵀ
john_loves_bill₀ = [ JOHN_LOVES_BILL₀ ]ᵀ (john , loves , bill , ∅)
--> john LOVES bill

SOMEONE_LOVES_MARY₀ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · np ·) ⊢[ s⁻ ]
SOMEONE_LOVES_MARY₀
  = ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ ( ↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))
someone_loves_mary₀ : ⟦ s⁻ ⟧ᵀ
someone_loves_mary₀ = [ SOMEONE_LOVES_MARY₀ ]ᵀ (someone , loves , mary , ∅)
--> exists (λ x → PERSON x ∧ x LOVES mary)

JOHN_LOVES_EVERYONE₀ : LG · np · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
JOHN_LOVES_EVERYONE₀
  = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ ( ↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻))))))))))))
john_loves_everyone₀ : ⟦ s⁻ ⟧ᵀ
john_loves_everyone₀ = [ JOHN_LOVES_EVERYONE₀ ]ᵀ (john , loves , everyone , ∅)
--> forAll (λ x → PERSON x ⊃ john LOVES x)

EVERYONE_LOVES_SOMEONE₀ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₀
  = ⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))
everyone_loves_someone₀ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₀ = [ EVERYONE_LOVES_SOMEONE₀ ]ᵀ (everyone , loves , someone , ∅)
--> forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ x LOVES y))

EVERYONE_LOVES_SOMEONE₁ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₁
  = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))
everyone_loves_someone₁ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₁ = [ EVERYONE_LOVES_SOMEONE₁ ]ᵀ (everyone , loves , someone , ∅)
--> exists (λ y → PERSON y ∧ forAll (λ y → PERSON x ⊃ x LOVES y))

EVERYONE_LOVES_SOMEONE₂ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₂
  = ⇁ (r⇐⊗ (⊗ᴸ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))
everyone_loves_someone₂ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₂ = [ EVERYONE_LOVES_SOMEONE₂ ]ᵀ (everyone , loves , someone , ∅)
--> exists (λ y → PERSON y ∧ forAll (λ y → PERSON x ⊃ x LOVES y))

EVERYONE_LOVES_SOMEONE₃ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₃
  = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))
everyone_loves_someone₃ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₃ = [ EVERYONE_LOVES_SOMEONE₃ ]ᵀ (everyone , loves , someone , ∅)
--> forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ x LOVES y))

EVERYONE_LOVES_SOMEONE₄ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₄
  = ⇁ (r⇐⊗ (⊗ᴸ (r⊗⇐ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))
everyone_loves_someone₄ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₄ = [ EVERYONE_LOVES_SOMEONE₄ ]ᵀ (everyone , loves , someone , ∅)
--> forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ x LOVES y))

EVERYONE_LOVES_SOMEONE₅ : LG · (np ⇐ n) ⊗ n · ⊗ (· (np ⇒ s⁻) ⇐ np · ⊗ · (np ⇐ n) ⊗ n ·) ⊢[ s⁻ ]
EVERYONE_LOVES_SOMEONE₅
  = ⇁ (r⇒⊗ (r⇒⊗ (⊗ᴸ (r⊗⇒ (r⊗⇒ (r⇐⊗ (⊗ᴸ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (⇒ᴸ ax⁺ ax⁻)))))))))))))))))))))))))))
everyone_loves_someone₅ : ⟦ s⁻ ⟧ᵀ
everyone_loves_someone₅ = [ EVERYONE_LOVES_SOMEONE₅ ]ᵀ (everyone , loves , someone , ∅)
--> exists (λ y → PERSON y ∧ forAll (λ x → PERSON x ⊃ x LOVES y))
