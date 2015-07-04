### Problems with Spurious Ambiguity
``` hidden
module spurious_ambiguity where

open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Example.System.Base using (Atom; N; NP; S; INF; _≟-Atom_)
open import Logic.Classical.Ordered.LambekGrishin.Type                Atom
open import Logic.Classical.Ordered.LambekGrishin.Judgement           Atom
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement    Atom
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Atom
open import Logic.Classical.Ordered.LambekGrishin.Base                Atom renaming (LG_ to NL_)
open import Logic.Classical.Ordered.LambekGrishin.ProofSearch         Atom _≟-Atom_ renaming (findAll to findAllNL)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.ProofSearch  Atom _≟-Atom_ renaming (findAll to findAllRM)
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
mary     = np
wants    = (np ⇒ s) ⇐ s
everyone = (np ⇐ n ) ⊗ n
to       = ((np ⇒ s ) ⇐ inf)
leave    = inf
```

```
testRM : length (findAllRM (mary ⊗ wants ⊗ everyone ⊗ to ⊗ leave ⊢ s)) ≡ 11
testRM = refl
```


```
testNL : length (findAllNL (· mary · ⊗ · wants · ⊗ · everyone · ⊗ · to · ⊗ · leave · ⊢[ s ])) ≡ 1664
testNL = refl
```
