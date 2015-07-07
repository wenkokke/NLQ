### Problems with Spurious Ambiguity
``` hidden
module nl_spurious_ambiguity where

open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Example.System.Base using (Atom; N; NP; S; INF; _≟-Atom_)
open import Logic.Intuitionistic.Ordered.Lambek.Type                Atom
open import Logic.Intuitionistic.Ordered.Lambek.Judgement           Atom as NL
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.Judgement    Atom as RM
open import Logic.Intuitionistic.Ordered.Lambek.Structure.Polarised Atom
open import Logic.Intuitionistic.Ordered.Lambek.Base                Atom
open import Logic.Intuitionistic.Ordered.Lambek.ProofSearch         Atom _≟-Atom_ renaming (findAll to findAllNL)
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.ProofSearch  Atom _≟-Atom_ renaming (findAll to findAllRM)
```

``` hidden
np n s inf : Type
np  = el NP
n   = el N
s   = el S
inf = el INF


mary wants everyone to leave : Type
```
```
mary      = np
wants     = (np ⇒ s) ⇐ s
everyone  = (np ⇐ n ) ⊗ n
to        = ((np ⇒ s ) ⇐ inf)
leave     = inf
```

``` hidden
testRM :
```
```
  length (findAllRM (
    mary ⊗ wants ⊗ everyone ⊗ to ⊗ leave ⊢ s)) ≡ 11
```
``` hidden
testRM = refl
```

``` hidden
testNL :
```
```
  length (findAllNL (
    · mary · ⊗ · wants · ⊗ · everyone · ⊗ · to · ⊗ · leave · ⊢[ s ])) ≡ 1664
```
``` hidden
testNL = refl
```
