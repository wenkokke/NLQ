## Assertions
```
module assertions where

open import Data.Bool                  using (Bool; true; false; _∧_)
open import Data.List                  using (List; _∷_; []; map; any; all)
open import Data.String                using (String; _++_)
open import Data.Unit                  using (⊤; tt)
open import Logic.Intuitionistic.Unrestricted.Agda.Show
open import Reflection
open import Relation.Nullary.Decidable using (⌊_⌋)
```

```
data AssertionFailed : String → Set where
```

```
assert : String → Bool → Term
assert msg true  = def (quote ⊤) []
assert msg false = def (quote AssertionFailed) (arg (arg-info visible relevant) (lit (string msg)) ∷ [])
```

```
list : Term → List Term
list (con (quote List._∷_) (_ ∷ _ ∷ arg _ y ∷ arg _ ys ∷ _)) = y ∷ list ys
list (con (quote List.[])   _                              ) = []
list y                                                       = y ∷ []
```

```
mutual
  drop-abs : Term → Term
  drop-abs (var x args)                                = var x (drop-abs-args args)
  drop-abs (con c args)                                = con c (drop-abs-args args)
  drop-abs (def f args)                                = def f (drop-abs-args args)
  drop-abs (lam v (abs _ x))                           = lam v (abs "_" (drop-abs x))
  drop-abs (pi (arg i (el s₁ t₁)) (abs _ (el s₂ t₂)))  = pi (arg i (el s₁ (drop-abs t₁))) (abs "_" (el s₂ (drop-abs t₂)))
  drop-abs t = t

  drop-abs-args : List (Arg Term) → List (Arg Term)
  drop-abs-args []               = []
  drop-abs-args (arg i x ∷ args) = arg i (drop-abs x) ∷ drop-abs-args args
```

```
_∈_ : Term → List Term → Bool
y ∈ xs = any (λ x → ⌊ x ≟ y ⌋) xs
```

```
_⇔_ : List Term → List Term → Bool
ys ⇔ xs = all (_∈ xs) ys ∧ all (_∈ ys) xs
```

``` hidden
infix 1 _↦_
```

```
macro
  _↦_ : Term → Term → Term
  act ↦ exp = assert
    ("Expected `" ++ show exp ++ "', found `" ++ show act ++ "'.")
    (map drop-abs (list act) ⇔ map drop-abs (list exp))
```
