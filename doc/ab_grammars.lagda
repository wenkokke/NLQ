# AB Grammars

``` hidden
module ab_grammars {ℓ} (Univ : Set ℓ) where
```

@barhillel1953 introduced two directional implications (written as
the division slashes |⇒| and |⇐|, based on the original division
notation by @ajdukiewicz1935).

```
data Type : Set ℓ where
  el   : Univ → Type
  _⇒_  : Type → Type → Type
  _⇐_  : Type → Type → Type
  _⊗_  : Type → Type → Type
```
