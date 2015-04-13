------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (id)
open import Data.Bool
open import Example.System.fLG


module Example.MaryThinksSomeoneLeft where


MARY_THINKS_SOMEONE_LEFT₀ : LG · np · ⊗ (· (np ⇒ s⁻) ⇐ s⁻ · ⊗ (· (np ⇐ n) ⊗ n · ⊗ · np ⇒ s⁻ ·)) ⊢[ s⁻ ]
MARY_THINKS_SOMEONE_LEFT₀ = ⇁ (r⇒⊗ (r⇐⊗ (↼ (⇐ᴸ (⇁ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻))))))))))) (⇒ᴸ ax⁺ ax⁻)))))
mary_thinks_someone_left₀ : ⟦ s⁻ ⟧ᵀ
mary_thinks_someone_left₀ = [ MARY_THINKS_SOMEONE_LEFT₀ ]ᵀ (mary , thinks , someone , left , ∅)
--> THINKS mary (exists (λ x → PERSON x ∧ LEFT x))

MARY_THINKS_SOMEONE_LEFT₁ : LG · np · ⊗ (· (np ⇒ s⁻) ⇐ s⁻ · ⊗ (· (np ⇐ n) ⊗ n · ⊗ · np ⇒ s⁻ ·)) ⊢[ s⁻ ]
MARY_THINKS_SOMEONE_LEFT₁ = ⇁ (r⇒⊗ (r⇒⊗ (r⇐⊗ (⊗ᴸ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ (⇁ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻)))) (⇒ᴸ ax⁺ ax⁻))))))))))))))
mary_thinks_someone_left₁ : ⟦ s⁻ ⟧ᵀ
mary_thinks_someone_left₁ = [ MARY_THINKS_SOMEONE_LEFT₁ ]ᵀ (mary , thinks , someone , left , ∅)
--> exists (λ x → PERSON x ∧ THINKS mary (LEFT x))

MARY_THINKS_SOMEONE_LEFT₂ : LG · np · ⊗ (· (np ⇒ s⁻) ⇐ s⁻ · ⊗ (· (np ⇐ n) ⊗ n · ⊗ · np ⇒ s⁻ ·)) ⊢[ s⁻ ]
MARY_THINKS_SOMEONE_LEFT₂ = ⇁ (r⇒⊗ (r⇒⊗ (r⇐⊗ (⊗ᴸ (r⊗⇐ (r⊗⇒ (r⇐⊗ (↼ (⇐ᴸ (⇁ (r⇐⊗ (r⇐⊗ (↼ (⇐ᴸ ax⁺ (↽ (r⊗⇐ (r⇒⊗ (↼ (⇒ᴸ ax⁺ ax⁻)))))))))) (⇒ᴸ ax⁺ ax⁻))))))))))
mary_thinks_someone_left₂ : ⟦ s⁻ ⟧ᵀ
mary_thinks_someone_left₂ = [ MARY_THINKS_SOMEONE_LEFT₂ ]ᵀ (mary , thinks , someone , left , ∅)
--> THINKS mary (exists (λ x → PERSON x ∧ LEFT x))
