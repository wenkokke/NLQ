------------------------------------------------------------------------
-- The Lambek Calculus in Agda
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

module Example.QuantifierRaisingInALG where


EVERYONE_LOVES_SOMEONE₀ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₀
  = (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax ax))) ax) (r⊕⇚ (r⇛⊕ (m⇛ ax ax))))))
everyone_loves_someone₀ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₀
  = [ EVERYONE_LOVES_SOMEONE₀ ]ᵀ (everyone , loves , someone) id
--> exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ LOVES y x))

EVERYONE_LOVES_SOMEONE₁ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₁
  = (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) (r⊕⇚ (r⇛⊕ (m⇛ ax ax))))))) ax))))
everyone_loves_someone₁ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₁
  = [ EVERYONE_LOVES_SOMEONE₁ ]ᵀ (everyone , loves , someone) id
--> forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ LOVES x y))

EVERYONE_LOVES_SOMEONE₂ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₂
  = (r⇒⊗ (r⇒⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ (r⊕⇚ (r⇛⊕ (m⇛ ax ax))) ax) ax))) ax)))))
everyone_loves_someone₂ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₂
  = [ EVERYONE_LOVES_SOMEONE₂ ]ᵀ (everyone , loves , someone) id
--> exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ LOVES y x))

EVERYONE_LOVES_SOMEONE₃ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₃
  = (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) ax))) ax)))))) ax))))
everyone_loves_someone₃ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₃
  = [ EVERYONE_LOVES_SOMEONE₃ ]ᵀ (everyone , loves , someone) id
--> forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ LOVES x y))

EVERYONE_LOVES_SOMEONE₄ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₄
  = (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax))))) (r⊕⇚ (r⇛⊕ (m⇛ ax ax))))))
everyone_loves_someone₄ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₄
  = [ EVERYONE_LOVES_SOMEONE₄ ]ᵀ (everyone , loves , someone) id
--> exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ LOVES y x))

EVERYONE_LOVES_SOMEONE₅ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₅
  = (r⇒⊗ (r⇒⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇒ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (m⇒ ax ax))) ax))))) ax))) ax)))))
everyone_loves_someone₅ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₅
  = [ EVERYONE_LOVES_SOMEONE₅ ]ᵀ (everyone , loves , someone) id
--> exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ LOVES y x))

EVERYONE_LOVES_SOMEONE₆ : LG ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ⊗ ( ( ( np ⇒ s⁻ ) ⇐ np ) ⊗ ( s⁻ ⇚ ( np ⇛ s⁻ ) ) ) ⊢ s⁻
EVERYONE_LOVES_SOMEONE₆
  = (r⇒⊗ (r⇒⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⊕⇚ (r⇛⊕ (m⇛ (r⊗⇐ (r⇒⊗ (r⇐⊗ (m⇐ (m⇒ ax ax) ax)))) ax)))))) ax)))))
everyone_loves_someone₆ : ⟦ s⁻  ⟧ᵀ
everyone_loves_someone₆
  = [ EVERYONE_LOVES_SOMEONE₆ ]ᵀ (everyone , loves , someone) id
--> exists (λ x → PERSON x ∧ forAll (λ y → PERSON y ⊃ LOVES y x))
