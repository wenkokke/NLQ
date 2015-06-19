------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Intuitionistic.Ordered.Lambek.SequentCalculus {ℓ} (Atom : Set ℓ) where


open import Logic.Intuitionistic.Ordered.Lambek.Type Atom


infixr 1 NL_
infix  2 _⊢_
infixr 4 _,_
infixr 4 _,>_
infixl 4 _<,_
infixl 3 _[_]


data Struct : Set ℓ where
  ·_·  : Type    → Struct
  _,_  : Struct  → Struct → Struct


data Context : Set ℓ where
  []    : Context
  _,>_  : Struct   → Context  → Context
  _<,_  : Context  → Struct   → Context


_[_] : Context → Struct → Struct
[]       [ Δ ] = Δ
Γ ,> Γ′  [ Δ ] = Γ , (Γ′ [ Δ ])
Γ <, Γ′  [ Δ ] = (Γ [ Δ ]) , Γ′


data Judgement : Set ℓ where
  _⊢_ : Struct → Type → Judgement


data NL_ : Judgement → Set ℓ where

  ax   : ∀ {A}
       →  NL · A · ⊢ A

  cut  : ∀ {Γ Δ A B}
       →  NL Γ ⊢ A → NL Δ [ · A · ] ⊢ B → NL Δ [ Γ ] ⊢ B

  ⊗L   : ∀ {Γ A B C}
       →  NL Γ [ · A · , · B · ] ⊢ C → NL Γ [ · A  ⊗ B · ] ⊢ C
  ⊗R   : ∀ {Γ Δ A B}
       →  NL Γ  ⊢ A → NL Δ ⊢ B → NL Γ , Δ ⊢ A ⊗ B

  ⇒L   : ∀ {Γ Δ A B C}
       →  NL Γ [ · B · ]  ⊢ C  →  NL Δ ⊢ A  →  NL Γ [ Δ , · A ⇒ B · ] ⊢ C
  ⇐L   : ∀ {Γ Δ A B C}
       →  NL Γ [ · B · ]  ⊢ C  →  NL Δ ⊢ A  →  NL Γ [ · B ⇐ A · , Δ ] ⊢ C

  ⇒R   : ∀ {Γ A B}
       →  NL · A · , Γ  ⊢ B  →  NL Γ  ⊢ A ⇒ B
  ⇐R   : ∀ {Γ A B}
       →  NL Γ , · A ·  ⊢ B  →  NL Γ  ⊢ B ⇐ A
