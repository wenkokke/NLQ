------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.NL.SC.Base {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type                 Atom
open import Logic.NL.SC.Structure         Atom
open import Logic.NL.SC.Structure.Context Atom
open import Logic.NL.SC.Judgement         Atom


infix 1 NL_ _⊢NL_


mutual
  _⊢NL_ : Structure → Type → Set ℓ
  Γ ⊢NL B = NL Γ ⊢ B
  

  data NL_ : Judgement → Set ℓ where
  
    ax   : ∀ {A}
         →  · A · ⊢NL A
  
    cut  : ∀ {Γ Δ A B}
         →  Γ ⊢NL A → Δ [ · A · ] ⊢NL B → Δ [ Γ ] ⊢NL B
    
    ⊗ᴸ   : ∀ {Γ A B C}
         →  Γ [ · A · , · B · ] ⊢NL C → Γ [ · A  ⊗ B · ] ⊢NL C
    ⊗ᴿ   : ∀ {Γ Δ A B}
         →  Γ  ⊢NL A → Δ ⊢NL B → Γ , Δ ⊢NL A ⊗ B
  
    ⇒ᴸ   : ∀ {Γ Δ A B C}
         →  Γ [ · B · ]  ⊢NL C  →  Δ ⊢NL A  →  Γ [ Δ , · A ⇒ B · ] ⊢NL C
    ⇐ᴸ   : ∀ {Γ Δ A B C}
         →  Γ [ · B · ]  ⊢NL C  →  Δ ⊢NL A  →  Γ [ · B ⇐ A · , Δ ] ⊢NL C
  
    ⇒ᴿ   : ∀ {Γ A B}
         →  · A · , Γ  ⊢NL B  →  Γ  ⊢NL A ⇒ B
    ⇐ᴿ   : ∀ {Γ A B}
         →  Γ , · A ·  ⊢NL B  →  Γ  ⊢NL B ⇐ A
