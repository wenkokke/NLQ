------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.List using (List; _∷_; [])
open import Function using (id)
open import Reflection using (Term)
open import Example.System.InSitu


module Example.QuantifierInSitu where


EVERYONE_LEFT₀ : NL ◇ ( s ⇦ ( □ np ⇨ s ) ) ⊗ ( np ⇒ s ) ⊢ s
EVERYONE_LEFT₀
  = (r⇐⊗ (Iᵢ (r⊗⇐ (Rᵢ (r⇦∘ (m⇦ ax (r∘⇨ (Rₑ (r⇒⊗ (m⇒ (Iₑ (r□◇ (m□ ax))) ax))))))))))
everyone_left₀ : ⟦ s  ⟧ᵀ
everyone_left₀
  = [ EVERYONE_LEFT₀ ]ᵀ (everyone , left)
--> forAll (λ x → PERSON x ⊃ LEFT x)


EVERYONE_LEFT₁ : NL ◇ ( s ⇦ ( □ np ⇨ s ) ) ⊗ ( np ⇒ s ) ⊢ s
EVERYONE_LEFT₁
  = (r⇐⊗ (Iᵢ (r⊗⇐ (Rᵢ (r⇦∘ (m⇦ ax (r∘⇨ (Rₑ (r⇐⊗ (Iₑ (r⊗⇐ (r⇒⊗ (m⇒ (r□◇ (m□ ax)) ax)))))))))))))
everyone_left₁ : ⟦ s  ⟧ᵀ
everyone_left₁
  = [ EVERYONE_LEFT₁ ]ᵀ (everyone , left)
--> forAll (λ x → PERSON x ⊃ LEFT x)


EVERYONE_LEFT₂ : NL ◇ ( s ⇦ ( □ np ⇨ s ) ) ⊗ ( np ⇒ s ) ⊢ s
EVERYONE_LEFT₂
  = (r⇐⊗ (Iᵢ (r⊗⇐ (Rᵢ (r⇦∘ (m⇦ ax (r∘⇨ (Rₑ (r⇐⊗ (Iₑ (r□◇ (m□ (r⊗⇐ (r⇒⊗ (m⇒ ax ax
  )))))))))))))))
everyone_left₂ : ⟦ s  ⟧ᵀ
everyone_left₂
  = [ EVERYONE_LEFT₂ ]ᵀ (everyone , left)
--> forAll (λ x → PERSON x ⊃ LEFT x)


JOHN_LOVES_EVERYONE₀ : NL np ⊗ ( ( ( np ⇒ s ) ⇐ np ) ⊗ ◇ ( s ⇦ ( □ np ⇨ s ) ) ) ⊢ s
JOHN_LOVES_EVERYONE₀
  = (r⇒⊗ (r⇒⊗ (Iᵢ (r⊗⇒ (Lᵢ (r⊗⇒ (Lᵢ (r⇦∘ (m⇦ ax (r∘⇨ (Lₑ (r⇒⊗ (Lₑ (r⇐⊗ (m⇐ (m⇒ ax ax) (Iₑ (r□◇ (m□ ax
  ))))))))))))))))))
john_loves_everyone₀ : ⟦ s  ⟧ᵀ
john_loves_everyone₀
  = [ JOHN_LOVES_EVERYONE₀ ]ᵀ (john , loves , everyone)
--> forAll (λ x → PERSON x ⊃ LOVES john x)

JOHN_LOVES_EVERYONE₁ : NL np ⊗ ( ( ( np ⇒ s ) ⇐ np ) ⊗ ◇ ( s ⇦ ( □ np ⇨ s ) ) ) ⊢ s
JOHN_LOVES_EVERYONE₁
  = (r⇒⊗ (r⇒⊗ (Iᵢ (r⊗⇒ (Lᵢ (r⊗⇒ (Lᵢ (r⇦∘ (m⇦ ax (r∘⇨ (Lₑ (r⇒⊗ (Lₑ (r⇒⊗ (Iₑ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) (r□◇ (m□ ax
  ))))))))))))))))))))
john_loves_everyone₁ : ⟦ s  ⟧ᵀ
john_loves_everyone₁
  = [ JOHN_LOVES_EVERYONE₁ ]ᵀ (john , loves , everyone)
--> forAll (λ x → PERSON x ⊃ LOVES john x)

JOHN_LOVES_EVERYONE₂ : NL np ⊗ ( ( ( np ⇒ s ) ⇐ np ) ⊗ ◇ ( s ⇦ ( □ np ⇨ s ) ) ) ⊢ s
JOHN_LOVES_EVERYONE₂
  = (r⇒⊗ (r⇒⊗ (Iᵢ (r⊗⇒ (Lᵢ (r⊗⇒ (Lᵢ (r⇦∘ (m⇦ ax (r∘⇨ (Lₑ (r⇒⊗ (Lₑ (r⇒⊗ (Iₑ (r□◇ (m□ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) ax
  ))))))))))))))))))))
john_loves_everyone₂ : ⟦ s  ⟧ᵀ
john_loves_everyone₂
  = [ JOHN_LOVES_EVERYONE₂ ]ᵀ (john , loves , everyone)
--> forAll (λ x → PERSON x ⊃ LOVES john x)


EVERYONE_LOVES_SOMEONE₀
  : NL ( ◇ ( s ⇦ ( □ np ⇨ s ) ) ) ⊗ ( ( np ⇒ s ) ⇐ np ) ⊗ ( ◇ ( s ⇦ ( □ np ⇨ s ) ) ) ⊢ s
EVERYONE_LOVES_SOMEONE₀
  = r⇐⊗ (Iᵢ (r⊗⇐ (Rᵢ (r⇦∘ (m⇦ ax (r∘⇨ (Rₑ (r⇐⊗ (Iₑ (r□◇ (m□ (r⊗⇐
  ( r⇒⊗ (r⇒⊗ (Iᵢ (r⊗⇒ (Lᵢ (r⊗⇒ (Lᵢ (r⇦∘ (m⇦ ax (r∘⇨ (Lₑ (r⇒⊗ (Lₑ (r⇒⊗ (Iₑ (r□◇ (m□ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ ax ax) ax
  ))))))))))))))))))))
  ))))))))))))
everyone_loves_someone₀  : ⟦ s  ⟧ᵀ
everyone_loves_someone₀
  = [ EVERYONE_LOVES_SOMEONE₀ ]ᵀ (everyone , loves , someone)
--> forAll (λ x → PERSON x ⊃ exists (λ x₁ → PERSON x₁ ∧ LOVES x x₁))


EVERYONE_LOVES_SOMEONE₁ : NL ◇ ( s ⇦ ( □ np ⇨ s ) ) ⊗ ( ( ( np ⇒ s ) ⇐ np ) ⊗ ◇ ( s ⇦ ( □ np ⇨ s ) ) ) ⊢ s
EVERYONE_LOVES_SOMEONE₁
  = (r⇐⊗ (Iᵢ (r⊗⇐ (Rᵢ (r⇦∘ (m⇦ ax (r∘⇨ (Rₑ (r⇒⊗ (r⇒⊗ (Iᵢ (r⊗⇒ (Lᵢ (r⊗⇒ (Lᵢ (r⇦∘ (m⇦ ax (r∘⇨ (Lₑ (r⇒⊗ (Lₑ (r⇐⊗ (m⇐ (m⇒ (Iₑ (r□◇ (m□ ax))) ax) (Iₑ (r□◇ (m□ ax))))))))))))))))))))))))))
everyone_loves_someone₁ : ⟦ s  ⟧ᵀ
everyone_loves_someone₁
  = [ EVERYONE_LOVES_SOMEONE₁ ]ᵀ (everyone , loves , someone)
--> forAll (λ x → PERSON x ⊃ exists (λ x₁ → PERSON x₁ ∧ LOVES x x₁))
