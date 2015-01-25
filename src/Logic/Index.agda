open import Algebra                               using (module Monoid)
open import Data.Nat                              using (ℕ; suc; zero)
open import Data.Fin                              using (Fin; suc; zero; #_)
open import Data.List                             using (List; map; length; _++_; _∷_; _∷ʳ_; [])
open import Data.Product                          using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)


module Logic.Index {a} {A : Set a} where


open Monoid (Data.List.monoid A) using (identity; assoc)


-- Given a list and an index which is guaranteed to be smaller than
-- the length of that list, return the element at the indicated
-- position in the list. 
lookup : (xs : List A) (i : Fin (length xs)) → A
lookup      []  (     )
lookup (x ∷ xs) (zero ) = x
lookup (x ∷ xs) (suc i) = lookup xs i


-- Given a list and an index which is guaranteed to be smaller than
-- the length of that list, return an index which is guaranteed to
-- return the same element (using |lookup|) from a list where one
-- element is moved forward.
forward : {x : _} (xs ys zs : List A) (i : _) → Σ[ j ∈ _ ]
          lookup (xs ++ ys ++ x ∷ zs) i ≡ lookup (xs ++ x ∷ ys ++ zs) j
forward (x ∷ xs) ys zs (suc i) with forward xs ys zs i
forward (x ∷ xs) ys zs (suc i) | j , p = suc j , p
forward (x ∷ xs) ys zs (zero ) = zero , refl
forward      []  ys zs (    i) = forward′ ys zs i
  where
  forward′  : {x : _ } (xs ys : List A) (i : _) → Σ[ j ∈ _ ]
              lookup (xs ++ x ∷ ys) i ≡ lookup (x ∷ xs ++ ys) j
  forward′      []  ys  i      =        i , refl
  forward′ (x ∷ xs) ys  zero   = suc zero , refl
  forward′ (x ∷ xs) ys (suc i) with forward′ xs ys i
  forward′ (x ∷ xs) ys (suc i) | zero  , p = zero        , p
  forward′ (x ∷ xs) ys (suc i) | suc j , p = suc (suc j) , p  


-- Given a list and an index which is guaranteed to be smaller than
-- the length of that list, return an index which is guaranteed to
-- return the same element (using |lookup|) from a list which is
-- permuted.
exchange : (xs ys zs ws : List A) (i : _) → Σ[ j ∈ _ ]
           lookup ((xs ++ zs) ++ (ys ++ ws)) i ≡ lookup ((xs ++ ys) ++ (zs ++ ws)) j
exchange xs ys zs ws i rewrite assoc xs zs (ys ++ ws)
                             | assoc xs ys (zs ++ ws) = exchange′ xs ys zs ws i
  where
  exchange′ : (xs ys zs ws : List A) (i : _) → Σ[ j ∈ _ ]
              lookup (xs ++ zs ++ ys ++ ws) i ≡ lookup (xs ++ ys ++ zs ++ ws) j
  exchange′ xs      []  zs ws i rewrite proj₂ identity xs | assoc xs zs ws = i , refl
  exchange′ xs (y ∷ ys) zs ws i = lem₃
    where
    lem₁ : Σ[ j ∈ _ ] lookup (xs ++ zs ++ y ∷ ys ++ ws) i ≡ lookup ((xs ∷ʳ y) ++ zs ++ ys ++ ws) j
    lem₁ rewrite sym (assoc (xs ∷ʳ y) zs (ys ++ ws))
               | assoc  xs (y ∷ []) zs
               | assoc  xs (y ∷ zs) (ys ++ ws) = forward xs zs (ys ++ ws) i

    lem₂ : Σ[ j ∈ _ ] lookup (xs ++ zs ++ y ∷ ys ++ ws) i ≡ lookup ((xs ∷ʳ y) ++ ys ++ zs ++ ws) j
    lem₂ with lem₁
    lem₂ | j , p with exchange′ (xs ∷ʳ y) ys zs ws j
    lem₂ | j , p | z , q = z , trans p q
    
    lem₃ : Σ[ j ∈ _ ] lookup (xs ++ zs ++ y ∷ ys ++ ws) i ≡ lookup (xs ++ y ∷ ys ++ zs ++ ws) j
    lem₃ rewrite sym (assoc xs (y ∷ ys) (zs ++ ws))
               | sym (assoc xs (y ∷ []) ys)
               | assoc (xs ∷ʳ y) ys (zs ++ ws) = lem₂

