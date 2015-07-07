## Syntactically Delimited Continuations

  ◇ᴸ  : ∀ {A Y}  → EXP ⟨ · A · ⟩ ⊢ Y → EXP · ◇ A · ⊢ Y
  ◇ᴿ  : ∀ {X B}  → EXP X ⊢[ B ] → EXP ⟨ X ⟩ ⊢[ ◇ B ]
