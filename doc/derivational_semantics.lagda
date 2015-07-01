``` hidden
open import Data.List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)


module derivational_semantics (Atom : Set) where

open import intermezzo_linear_logic         Atom as ILL
open import non_associative_lambek_calculus Atom as NL
open module RM = NL.ResMon hiding (_[_])
```

# Derivational Semantics

```
⟦_⟧ : NL.Type → ILL.Type
⟦ el   A  ⟧ = el  A
⟦ A ⊗  B  ⟧ = ⟦ A ⟧ ⊗  ⟦ B ⟧
⟦ A ⇒  B  ⟧ = ⟦ A ⟧ ⊸  ⟦ B ⟧
⟦ B ⇐  A  ⟧ = ⟦ A ⟧ ⊸  ⟦ B ⟧
```

```
[_] : ∀ {A B} → RM A RM.⊢ B → ILL ⟦ A ⟧ , ∅ ILL.⊢ ⟦ B ⟧
[ ax       ] = ax
[ m⊗   f g ] = ⊗ₑ ax (⊗ᵢ [ f ] [ g ])
[ m⇒   f g ] = ⊸ᵢ (⊸ₑ (⊸ᵢ [ g  ]) (e₁ (⊸ₑ ax [ f  ])))
[ m⇐   f g ] = ⊸ᵢ (⊸ₑ (⊸ᵢ [ f  ]) (e₁ (⊸ₑ ax [ g  ])))
[ r⇒⊗  f   ] = ⊗ₑ ax (e₁  (⊸ₑ [ f ] ax))
[ r⇐⊗  f   ] = ⊗ₑ ax (    (⊸ₑ [ f ] ax))
[ r⊗⇒  f   ] = ⊸ᵢ (    (⊸ₑ (⊸ᵢ [ f ]) (⊗ᵢ ax ax)))
[ r⊗⇐  f   ] = ⊸ᵢ (e₁  (⊸ₑ (⊸ᵢ [ f ]) (⊗ᵢ ax ax)))
```
