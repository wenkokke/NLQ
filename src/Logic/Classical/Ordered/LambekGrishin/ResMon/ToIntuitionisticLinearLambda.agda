------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra                               using (module Monoid)
open import Function                              using (id; _∘_)
open import Data.List                             using (List; _++_; monoid) renaming (_∷_ to _,_; [] to ∅)
open import Relation.Binary.PropositionalEquality using (sym)


module Logic.Classical.Ordered.LambekGrishin.ResMon.ToIntuitionisticLinearLambda {ℓ} (Univ : Set ℓ) (⊥ : Univ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.Classical.Ordered.LambekGrishin.Type             Univ as LG
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement Univ as LGJ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base      Univ

open import Logic.Intuitionistic.Linear.Lambda.Type      Univ as Λ
open import Logic.Intuitionistic.Linear.Lambda.Judgement Univ as ΛJ
open import Logic.Intuitionistic.Linear.Lambda.Base      Univ
open import Logic.Intuitionistic.Linear.Lambda.Permute   Univ

open Monoid (monoid Λ.Type) using (assoc)



-- * Intuitionistic Linear Negation

infixr 50 ¬_

¬_ : Λ.Type → Λ.Type
¬ A = A ⇒ el ⊥

¬¬ : ∀ {A} → Λ A , ∅ ⊢ ¬ ¬ A
¬¬ = ⇒ᵢ (⇒ₑ ax ax)

contra : ∀ {A B} → Λ A , ∅ ⊢ B → Λ ¬ B , ∅ ⊢ ¬ A
contra f = ⇒ᵢ (eᴸ₁ (⇒ₑ ax f))

deMorgan : ∀ {A B} → Λ ¬ ¬ A ⊗ ¬ ¬ B , ∅ ⊢ ¬ ¬ (A ⊗ B)
deMorgan = ⊗ₑ ax (⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (eᴸ₂ (⇒ₑ ax (⇒ᵢ (eᴸ₂ (⇒ₑ ax (eᴸ₁ (⊗ᵢ ax ax)))))))))))



-- * Call-by-value translation

⌈_⌉ : LG.Type → Λ.Type
⌈ el  A ⌉ = el A
⌈ ◇   A ⌉ =      ⌈ A ⌉
⌈ □   A ⌉ =      ⌈ A ⌉
⌈ ₀   A ⌉ = ¬    ⌈ A ⌉
⌈ A   ⁰ ⌉ = ¬    ⌈ A ⌉
⌈ ₁   A ⌉ = ¬    ⌈ A ⌉
⌈ A   ¹ ⌉ = ¬    ⌈ A ⌉
⌈ A ⊗ B ⌉ =   (  ⌈ A ⌉ ⊗   ⌈ B ⌉)
⌈ A ⇒ B ⌉ = ¬ (  ⌈ A ⌉ ⊗ ¬ ⌈ B ⌉)
⌈ B ⇐ A ⌉ = ¬ (¬ ⌈ B ⌉ ⊗   ⌈ A ⌉)
⌈ B ⊕ A ⌉ = ¬ (¬ ⌈ B ⌉ ⊗ ¬ ⌈ A ⌉)
⌈ B ⇚ A ⌉ =   (  ⌈ B ⌉ ⊗ ¬ ⌈ A ⌉)
⌈ A ⇛ B ⌉ =   (¬ ⌈ A ⌉ ⊗   ⌈ B ⌉)


mutual
  ⌈_⌉ᴸ : ∀ {A B} → LG A ⊢ B → Λ ¬ ⌈ B ⌉ , ∅ ⊢ ¬ ⌈ A ⌉
  ⌈ ax       ⌉ᴸ = contra ax
  ⌈ m□  f    ⌉ᴸ = ⌈ f ⌉ᴸ
  ⌈ m◇  f    ⌉ᴸ = ⌈ f ⌉ᴸ
  ⌈ r□◇ f    ⌉ᴸ = ⌈ f ⌉ᴸ
  ⌈ r◇□ f    ⌉ᴸ = ⌈ f ⌉ᴸ
  ⌈ m⁰  f    ⌉ᴸ = contra (⇒ᵢ (⇒ₑ ⌈ f ⌉ᴿ ax))
  ⌈ m₀  f    ⌉ᴸ = contra (⇒ᵢ (⇒ₑ ⌈ f ⌉ᴿ ax))
  ⌈ r⁰₀ f    ⌉ᴸ = contra (⇒ᵢ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉ᴸ ax))))
  ⌈ r₀⁰ f    ⌉ᴸ = contra (⇒ᵢ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉ᴸ ax))))
  ⌈ m₁  f    ⌉ᴸ = contra (⇒ᵢ (⇒ₑ ⌈ f ⌉ᴿ ax))
  ⌈ m¹  f    ⌉ᴸ = contra (⇒ᵢ (⇒ₑ ⌈ f ⌉ᴿ ax))
  ⌈ r¹₁ f    ⌉ᴸ = ⇒ᵢ (⇒ₑ ⌈ f ⌉ᴸ ax)
  ⌈ r₁¹ f    ⌉ᴸ = ⇒ᵢ (⇒ₑ ⌈ f ⌉ᴸ ax)
  ⌈ r⇒⊗ f    ⌉ᴸ = ⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉ᴸ ax)))))
  ⌈ r⊗⇒ f    ⌉ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (eᴸ₁ (⇒ₑ ⌈ f ⌉ᴸ ax))))))
  ⌈ r⇐⊗ f    ⌉ᴸ = ⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉ᴸ ax)))))
  ⌈ r⊗⇐ f    ⌉ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (eᴸ₁ (⇒ₑ ⌈ f ⌉ᴸ ax))))))
  ⌈ m⊗  f g  ⌉ᴸ = ⇒ᵢ (⇒ₑ (cut′ (⊗ₑᴸ₁ (⊗ᵢ ⌈ f ⌉ᴿ ⌈ g ⌉ᴿ)) deMorgan) ax)
  ⌈ m⇒  f g  ⌉ᴸ = contra (⇒ᵢ (⇒ₑ (cut′ (⊗ₑᴸ₁ (⊗ᵢ ⌈ f ⌉ᴿ (⇒ᵢ (⇒ₑ ax ⌈ g ⌉ᴸ)))) deMorgan) ax))
  ⌈ m⇐  f g  ⌉ᴸ = contra (⇒ᵢ (⇒ₑ (cut′ (⊗ₑᴸ₁ (⊗ᵢ (⇒ᵢ (⇒ₑ ax ⌈ f ⌉ᴸ)) ⌈ g ⌉ᴿ)) deMorgan) ax))
  ⌈ r⇛⊕ f    ⌉ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (eᴸ₁ (⇒ₑ ⌈ f ⌉ᴸ ax))))))
  ⌈ r⊕⇛ f    ⌉ᴸ = ⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉ᴸ ax)))))
  ⌈ r⇚⊕ f    ⌉ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (eᴸ₁ (⇒ₑ ⌈ f ⌉ᴸ ax))))))
  ⌈ r⊕⇚ f    ⌉ᴸ = ⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉ᴸ ax)))))
  ⌈ m⊕  f g  ⌉ᴸ = contra (contra (⊗ₑᴸ₁ (⊗ᵢ ⌈ f ⌉ᴸ ⌈ g ⌉ᴸ)))
  ⌈ m⇛  f g  ⌉ᴸ = ⇒ᵢ (⇒ₑ (cut′ (⊗ₑᴸ₁ (⊗ᵢ (⇒ᵢ (⇒ₑ ax ⌈ f ⌉ᴸ)) ⌈ g ⌉ᴿ)) deMorgan) ax)
  ⌈ m⇚  f g  ⌉ᴸ = ⇒ᵢ (⇒ₑ (cut′ (⊗ₑᴸ₁ (⊗ᵢ ⌈ f ⌉ᴿ (⇒ᵢ (⇒ₑ ax ⌈ g ⌉ᴸ)))) deMorgan) ax)
  ⌈ d⇛⇐ f    ⌉ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (eᴸ₂′ (⊗ᵢᴸ₁ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉ᴸ ax)))))))))))
  ⌈ d⇛⇒ f    ⌉ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂ (⊗ₑᴸ₁ (e₁₃ (⊗ᵢᴸ₁ (eᴸ₂′ (⊗ᵢᴸ₁ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉ᴸ ax)))))))))))
  ⌈ d⇚⇒ f    ⌉ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂ (⊗ₑᴸ₁ (e₀₃ (⊗ᵢᴸ₁ (eᴸ₂′ (⊗ᵢᴸ₁ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉ᴸ ax)))))))))))
  ⌈ d⇚⇐ f    ⌉ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (eᴸ₂′ (⊗ᵢᴸ₁ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉ᴸ ax)))))))))))

  ⌈_⌉ᴿ : ∀ {A B} → LG A ⊢ B → Λ ⌈ A ⌉ , ∅ ⊢ ¬ ¬ ⌈ B ⌉
  ⌈ ax       ⌉ᴿ = ¬¬
  ⌈ m□  f    ⌉ᴿ = ⌈ f ⌉ᴿ
  ⌈ m◇  f    ⌉ᴿ = ⌈ f ⌉ᴿ
  ⌈ r□◇ f    ⌉ᴿ = ⌈ f ⌉ᴿ
  ⌈ r◇□ f    ⌉ᴿ = ⌈ f ⌉ᴿ
  ⌈ m⁰  f    ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⇒ₑ ⌈ f ⌉ᴿ ax)))
  ⌈ m₀  f    ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⇒ₑ ⌈ f ⌉ᴿ ax)))
  ⌈ r⁰₀ f    ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (eᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax))))))
  ⌈ r₀⁰ f    ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (eᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax))))))
  ⌈ m₁  f    ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⇒ₑ ⌈ f ⌉ᴿ ax)))
  ⌈ m¹  f    ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⇒ₑ ⌈ f ⌉ᴿ ax)))
  ⌈ r¹₁ f    ⌉ᴿ = ⌈ f ⌉ᴸ
  ⌈ r₁¹ f    ⌉ᴿ = ⌈ f ⌉ᴸ
  ⌈ r⇒⊗ f    ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (e₀₁ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax))))))
  ⌈ r⊗⇒ f    ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax))))))
  ⌈ r⇐⊗ f    ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (e₁₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax))))))
  ⌈ r⊗⇐ f    ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax))))))
  ⌈ m⊗  f g  ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (eᴸ₂′ (⇒ₑ (cut′ (⊗ᵢ ⌈ f ⌉ᴿ ⌈ g ⌉ᴿ) deMorgan) ax)))
  ⌈ m⇒  f g  ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (⇒ₑ (cut′ (⊗ᵢ ⌈ f ⌉ᴿ (⇒ᵢ (⇒ₑ ax ⌈ g ⌉ᴸ))) deMorgan) ax))))
  ⌈ m⇐  f g  ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (⇒ₑ (cut′ (⊗ᵢ (⇒ᵢ (⇒ₑ ax ⌈ f ⌉ᴸ)) ⌈ g ⌉ᴿ) deMorgan) ax))))
  ⌈ r⇛⊕ f    ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax))))))
  ⌈ r⊕⇛ f    ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (e₀₁ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax))))))
  ⌈ r⇚⊕ f    ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax))))))
  ⌈ r⊕⇚ f    ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (e₁₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax))))))
  ⌈ m⊕  f g  ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂ (⇒ₑ ax (⊗ᵢ ⌈ f ⌉ᴸ ⌈ g ⌉ᴸ))))))
  ⌈ m⇛  f g  ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (eᴸ₂′ (⇒ₑ (cut′ (⊗ᵢ (⇒ᵢ (⇒ₑ ax ⌈ f ⌉ᴸ)) ⌈ g ⌉ᴿ) deMorgan) ax)))
  ⌈ m⇚  f g  ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (eᴸ₂′ (⇒ₑ (cut′ (⊗ᵢ ⌈ f ⌉ᴿ (⇒ᵢ (⇒ₑ ax ⌈ g ⌉ᴸ))) deMorgan) ax)))
  ⌈ d⇛⇐ f    ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂  (e₂₃ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₂′ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax)))))))))))
  ⌈ d⇛⇒ f    ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (     (e₀₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₂′ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax)))))))))))
  ⌈ d⇚⇒ f    ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂′ (e₁₃ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₂′ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax)))))))))))
  ⌈ d⇚⇐ f    ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (     (e₁₃ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₂′ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉ᴿ ax)))))))))))


⌈_⌉ᴶ : LGJ.Judgement → ΛJ.Judgement
⌈ A ⊢ B ⌉ᴶ = ⌈ A ⌉ , ∅ ⊢ ¬ ¬ ⌈ B ⌉


CBV : Translation LG.Type Λ.Type LG_ Λ_
CBV = record
  { ⟦_⟧ᵀ = ⌈_⌉
  ; ⟦_⟧ᴶ = ⌈_⌉ᴶ
  ; [_]  = λ { {_ ⊢ _} → ⌈_⌉ᴿ }
  }



-- * Call-by-name translation

⌊_⌋ : LG.Type → Λ.Type
⌊ A ⌋ = ⌈ A ∞ ⌉


⌊_⌋ᴸ : ∀ {A B} → LG A ⊢ B → Λ ¬ ⌊ A ⌋ , ∅ ⊢ ¬ ⌊ B ⌋
⌊_⌋ᴸ = ⌈_⌉ᴸ ∘ _∞ᵗ

⌊_⌋ᴿ : ∀ {A B} → LG A ⊢ B → Λ ⌊ B ⌋ , ∅ ⊢ ¬ ¬ ⌊ A ⌋
⌊_⌋ᴿ = ⌈_⌉ᴿ ∘ _∞ᵗ


⌊_⌋ᴶ : LGJ.Judgement → ΛJ.Judgement
⌊ A ⊢ B ⌋ᴶ = ¬ ⌊ A ⌋ , ∅ ⊢ ¬ ⌊ B ⌋


CBN : Translation LG.Type Λ.Type LG_ Λ_
CBN = record
  { ⟦_⟧ᵀ = ⌊_⌋
  ; ⟦_⟧ᴶ = ⌊_⌋ᴶ
  ; [_]  = λ { {_ ⊢ _} → ⌊_⌋ᴸ }
  }



-- * Alternative call-by-value translation

⌈_⌉′ : LG.Type → Λ.Type
⌈ el  A ⌉′ = el A
⌈ ◇   A ⌉′ =        ⌈ A ⌉′
⌈ □   A ⌉′ =        ⌈ A ⌉′
⌈ ₀   A ⌉′ = ¬      ⌈ A ⌉′
⌈ A   ⁰ ⌉′ = ¬      ⌈ A ⌉′
⌈ ₁   A ⌉′ = ¬      ⌈ A ⌉′
⌈ A   ¹ ⌉′ = ¬      ⌈ A ⌉′
⌈ A ⊗ B ⌉′ =     (  ⌈ A ⌉′ ⊗   ⌈ B ⌉′)
⌈ A ⇒ B ⌉′ = ¬   (  ⌈ A ⌉′ ⊗ ¬ ⌈ B ⌉′)
⌈ B ⇐ A ⌉′ = ¬   (¬ ⌈ B ⌉′ ⊗   ⌈ A ⌉′)
⌈ B ⊕ A ⌉′ = ¬   (¬ ⌈ B ⌉′ ⊗ ¬ ⌈ A ⌉′)
⌈ B ⇚ A ⌉′ = ¬ ¬ (  ⌈ B ⌉′ ⊗ ¬ ⌈ A ⌉′)
⌈ A ⇛ B ⌉′ = ¬ ¬ (¬ ⌈ A ⌉′ ⊗   ⌈ B ⌉′)


mutual
  ⌈_⌉′ᴸ : ∀ {A B} → LG A ⊢ B → Λ ¬ ⌈ B ⌉′ , ∅ ⊢ ¬ ⌈ A ⌉′
  ⌈ ax       ⌉′ᴸ = contra ax
  ⌈ m□  f    ⌉′ᴸ = ⌈ f ⌉′ᴸ
  ⌈ m◇  f    ⌉′ᴸ = ⌈ f ⌉′ᴸ
  ⌈ r□◇ f    ⌉′ᴸ = ⌈ f ⌉′ᴸ
  ⌈ r◇□ f    ⌉′ᴸ = ⌈ f ⌉′ᴸ
  ⌈ m⁰  f    ⌉′ᴸ = contra (⇒ᵢ (⇒ₑ ⌈ f ⌉′ᴿ ax))
  ⌈ m₀  f    ⌉′ᴸ = contra (⇒ᵢ (⇒ₑ ⌈ f ⌉′ᴿ ax))
  ⌈ r⁰₀ f    ⌉′ᴸ = contra (⇒ᵢ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴸ ax))))
  ⌈ r₀⁰ f    ⌉′ᴸ = contra (⇒ᵢ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴸ ax))))
  ⌈ m₁  f    ⌉′ᴸ = contra (⇒ᵢ (⇒ₑ ⌈ f ⌉′ᴿ ax))
  ⌈ m¹  f    ⌉′ᴸ = contra (⇒ᵢ (⇒ₑ ⌈ f ⌉′ᴿ ax))
  ⌈ r¹₁ f    ⌉′ᴸ = ⇒ᵢ (⇒ₑ ⌈ f ⌉′ᴸ ax)
  ⌈ r₁¹ f    ⌉′ᴸ = ⇒ᵢ (⇒ₑ ⌈ f ⌉′ᴸ ax)
  ⌈ r⇒⊗ f    ⌉′ᴸ = ⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴸ ax)))))
  ⌈ r⊗⇒ f    ⌉′ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (eᴸ₁ (⇒ₑ ⌈ f ⌉′ᴸ ax))))))
  ⌈ r⇐⊗ f    ⌉′ᴸ = ⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴸ ax)))))
  ⌈ r⊗⇐ f    ⌉′ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (eᴸ₁ (⇒ₑ ⌈ f ⌉′ᴸ ax))))))
  ⌈ m⊗  f g  ⌉′ᴸ = ⇒ᵢ (⇒ₑ (cut′ (⊗ₑᴸ₁ (⊗ᵢ ⌈ f ⌉′ᴿ ⌈ g ⌉′ᴿ)) deMorgan) ax)
  ⌈ m⇒  f g  ⌉′ᴸ = contra (⇒ᵢ (⇒ₑ (cut′ (⊗ₑᴸ₁ (⊗ᵢ ⌈ f ⌉′ᴿ (⇒ᵢ (⇒ₑ ax ⌈ g ⌉′ᴸ)))) deMorgan) ax))
  ⌈ m⇐  f g  ⌉′ᴸ = contra (⇒ᵢ (⇒ₑ (cut′ (⊗ₑᴸ₁ (⊗ᵢ (⇒ᵢ (⇒ₑ ax ⌈ f ⌉′ᴸ)) ⌈ g ⌉′ᴿ)) deMorgan) ax))
  ⌈ r⇛⊕ f    ⌉′ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉′ᴸ ax)))))))
  ⌈ r⊕⇛ f    ⌉′ᴸ = cut′ (⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴸ ax)))))) ¬¬
  ⌈ r⇚⊕ f    ⌉′ᴸ = contra (⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉′ᴸ ax)))))))
  ⌈ r⊕⇚ f    ⌉′ᴸ = cut′ (⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴸ ax)))))) ¬¬
  ⌈ m⊕  f g  ⌉′ᴸ = contra (contra (⊗ₑᴸ₁ (⊗ᵢ ⌈ f ⌉′ᴸ ⌈ g ⌉′ᴸ)))
  ⌈ m⇛  f g  ⌉′ᴸ = cut′ (⇒ᵢ (⇒ₑ (cut′ (cut′ (⊗ₑᴸ₁ (⊗ᵢ (⇒ᵢ (⇒ₑ ax ⌈ f ⌉′ᴸ)) ⌈ g ⌉′ᴿ)) deMorgan) ¬¬) ax)) ¬¬
  ⌈ m⇚  f g  ⌉′ᴸ = cut′ (⇒ᵢ (⇒ₑ (cut′ (cut′ (⊗ₑᴸ₁ (⊗ᵢ ⌈ f ⌉′ᴿ (⇒ᵢ (⇒ₑ ax ⌈ g ⌉′ᴸ)))) deMorgan) ¬¬) ax)) ¬¬
  ⌈ d⇛⇐ f    ⌉′ᴸ = cut′ (contra (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (eᴸ₂′ (⊗ᵢᴸ₁ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴸ ax)))))))))))) ¬¬
  ⌈ d⇛⇒ f    ⌉′ᴸ = cut′ (contra (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂ (⊗ₑᴸ₁ (e₁₃ (⊗ᵢᴸ₁ (eᴸ₂′ (⊗ᵢᴸ₁ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴸ ax)))))))))))) ¬¬
  ⌈ d⇚⇒ f    ⌉′ᴸ = cut′ (contra (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂ (⊗ₑᴸ₁ (e₀₃ (⊗ᵢᴸ₁ (eᴸ₂′ (⊗ᵢᴸ₁ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴸ ax)))))))))))) ¬¬
  ⌈ d⇚⇐ f    ⌉′ᴸ = cut′ (contra (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (eᴸ₂′ (⊗ᵢᴸ₁ (eᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴸ ax)))))))))))) ¬¬

  ⌈_⌉′ᴿ : ∀ {A B} → LG A ⊢ B → Λ ⌈ A ⌉′ , ∅ ⊢ ¬ ¬ ⌈ B ⌉′
  ⌈ ax       ⌉′ᴿ = ¬¬
  ⌈ m□  f    ⌉′ᴿ = ⌈ f ⌉′ᴿ
  ⌈ m◇  f    ⌉′ᴿ = ⌈ f ⌉′ᴿ
  ⌈ r□◇ f    ⌉′ᴿ = ⌈ f ⌉′ᴿ
  ⌈ r◇□ f    ⌉′ᴿ = ⌈ f ⌉′ᴿ
  ⌈ m⁰  f    ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⇒ₑ ⌈ f ⌉′ᴿ ax)))
  ⌈ m₀  f    ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⇒ₑ ⌈ f ⌉′ᴿ ax)))
  ⌈ r⁰₀ f    ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (eᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax))))))
  ⌈ r₀⁰ f    ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (eᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax))))))
  ⌈ m₁  f    ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⇒ₑ ⌈ f ⌉′ᴿ ax)))
  ⌈ m¹  f    ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⇒ₑ ⌈ f ⌉′ᴿ ax)))
  ⌈ r¹₁ f    ⌉′ᴿ = ⌈ f ⌉′ᴸ
  ⌈ r₁¹ f    ⌉′ᴿ = ⌈ f ⌉′ᴸ
  ⌈ r⇒⊗ f    ⌉′ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (e₀₁ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax))))))
  ⌈ r⊗⇒ f    ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax))))))
  ⌈ r⇐⊗ f    ⌉′ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (e₁₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax))))))
  ⌈ r⊗⇐ f    ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax))))))
  ⌈ m⊗  f g  ⌉′ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (eᴸ₂′ (⇒ₑ (cut′ (⊗ᵢ ⌈ f ⌉′ᴿ ⌈ g ⌉′ᴿ) deMorgan) ax)))
  ⌈ m⇒  f g  ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (⇒ₑ (cut′ (⊗ᵢ ⌈ f ⌉′ᴿ (⇒ᵢ (⇒ₑ ax ⌈ g ⌉′ᴸ))) deMorgan) ax))))
  ⌈ m⇐  f g  ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (⇒ₑ (cut′ (⊗ᵢ (⇒ᵢ (⇒ₑ ax ⌈ f ⌉′ᴸ)) ⌈ g ⌉′ᴿ) deMorgan) ax))))
  ⌈ r⇛⊕ f    ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (e₁₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴿ ax)))))))
  ⌈ r⊕⇛ f    ⌉′ᴿ = ⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (⇒ₑ (⊗ₑᴸ₁ (⇒ᵢ (e₀₁ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax))))))) ax))))
  ⌈ r⇚⊕ f    ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (e₀₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (⇒ₑ ⌈ f ⌉′ᴿ ax)))))))
  ⌈ r⊕⇚ f    ⌉′ᴿ = ⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (⇒ₑ (⊗ₑᴸ₁ (⇒ᵢ (e₁₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax))))))) ax))))
  ⌈ m⊕  f g  ⌉′ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂ (⇒ₑ ax (⊗ᵢ ⌈ f ⌉′ᴸ ⌈ g ⌉′ᴸ))))))
  ⌈ m⇛  f g  ⌉′ᴿ = ⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (⇒ₑ (cut′ (⊗ₑᴸ₁ (⇒ᵢ (eᴸ₂′ (⇒ₑ (cut′ (⊗ᵢ (⇒ᵢ (⇒ₑ ax ⌈ f ⌉′ᴸ)) ⌈ g ⌉′ᴿ) deMorgan) ax)))) ¬¬) ax))))
  ⌈ m⇚  f g  ⌉′ᴿ = ⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (⇒ₑ (cut′ (⊗ₑᴸ₁ (⇒ᵢ (eᴸ₂′ (⇒ₑ (cut′ (⊗ᵢ ⌈ f ⌉′ᴿ (⇒ᵢ (⇒ₑ ax ⌈ g ⌉′ᴸ))) deMorgan) ax)))) ¬¬) ax))))
  ⌈ d⇛⇐ f    ⌉′ᴿ = ⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (⇒ₑ (⊗ₑᴸ₁ (⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂  (e₂₃ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₂′ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax)))))))))))) ax))))
  ⌈ d⇛⇒ f    ⌉′ᴿ = ⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (⇒ₑ (⊗ₑᴸ₁ (⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (     (e₀₂ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₂′ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax)))))))))))) ax))))
  ⌈ d⇚⇒ f    ⌉′ᴿ = ⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (⇒ₑ (⊗ₑᴸ₁ (⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₂′ (e₁₃ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₂′ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax)))))))))))) ax))))
  ⌈ d⇚⇐ f    ⌉′ᴿ = ⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (⇒ₑ (⊗ₑᴸ₁ (⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (     (e₁₃ (⊗ᵢᴸ₁ (cut′ ¬¬ (eᴸ₂′ (⊗ᵢᴸ₁ (⇒ₑ ⌈ f ⌉′ᴿ ax)))))))))))) ax))))


⌈_⌉′ᴶ : LGJ.Judgement → ΛJ.Judgement
⌈ A ⊢ B ⌉′ᴶ = ⌈ A ⌉′ , ∅ ⊢ ¬ ¬ ⌈ B ⌉′


CBV′ : Translation LG.Type Λ.Type LG_ Λ_
CBV′ = record
  { ⟦_⟧ᵀ = ⌈_⌉′
  ; ⟦_⟧ᴶ = ⌈_⌉′ᴶ
  ; [_]  = λ { {_ ⊢ _} → ⌈_⌉′ᴿ }
  }
