------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Algebra                               using (module Monoid)
open import Data.Nat                              using (ℕ; suc; zero)
open import Data.Fin                              using (Fin; suc; zero; #_)
open import Data.List                             using (List; map; length; _++_; _∷_; _∷ʳ_; [])
open import Data.Product                          using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)


module Logic.Index where


infix 90 _‼_


-- Given a list and an index which is guaranteed to be smaller than
-- the length of that list, return the element at the indicated
-- position in the list.
_‼_ : ∀ {a} {A : Set a} (xs : List A) (i : Fin (length xs)) → A
(    []) ‼ (     )
(x ∷ xs) ‼ (zero ) = x
(x ∷ xs) ‼ (suc i) = xs ‼ i


-- Given a list and an index which is guaranteed to be smaller than
-- the length of that list, return an index which is guaranteed to
-- return the same element (using |lookup|) from a list where one
-- element is moved forward.
forward : ∀ {a} {A : Set a} {x : _} (xs ys zs : List A) (i : _) → Σ[ j ∈ _ ]
          (xs ++ ys ++ x ∷ zs) ‼ i ≡ (xs ++ x ∷ ys ++ zs) ‼ j
forward (x ∷ xs) ys zs (suc i) with forward xs ys zs i
forward (x ∷ xs) ys zs (suc i) | j , p = suc j , p
forward (x ∷ xs) ys zs (zero ) = zero , refl
forward      []  ys zs (    i) = forward′ ys zs i
  where
  forward′  : ∀ {a} {A : Set a} {x : _ } (xs ys : List A) (i : _) → Σ[ j ∈ _ ]
              (xs ++ x ∷ ys) ‼ i ≡ (x ∷ xs ++ ys) ‼ j
  forward′      []  ys  i      =        i , refl
  forward′ (x ∷ xs) ys  zero   = suc zero , refl
  forward′ (x ∷ xs) ys (suc i) with forward′ xs ys i
  forward′ (x ∷ xs) ys (suc i) | zero  , p = zero        , p
  forward′ (x ∷ xs) ys (suc i) | suc j , p = suc (suc j) , p


-- Given a list and an index which is guaranteed to be smaller than
-- the length of that list, return an index which is guaranteed to
-- return the same element (using |lookup|) from a list which is
-- permuted.
exchange : ∀ {a} {A : Set a} (xs ys zs ws : List A) (i : _) → Σ[ j ∈ _ ]
           ((xs ++ zs) ++ (ys ++ ws)) ‼ i ≡ ((xs ++ ys) ++ (zs ++ ws)) ‼ j
exchange {a} {A} = exchange′
  where
  open Monoid (Data.List.monoid A) using (assoc; identity)

  exchange′ : (xs ys zs ws : List A) (i : _) → Σ[ j ∈ _ ]
              ((xs ++ zs) ++ (ys ++ ws)) ‼ i ≡ ((xs ++ ys) ++ (zs ++ ws)) ‼ j
  exchange′ xs ys zs ws i rewrite assoc xs zs (ys ++ ws)
                                | assoc xs ys (zs ++ ws) = exchange″ xs ys zs ws i
    where
    exchange″ : (xs ys zs ws : List A) (i : _) → Σ[ j ∈ _ ]
                (xs ++ zs ++ ys ++ ws) ‼ i ≡ (xs ++ ys ++ zs ++ ws) ‼ j
    exchange″ xs      []  zs ws i rewrite proj₂ identity xs | assoc xs zs ws = i , refl
    exchange″ xs (y ∷ ys) zs ws i = lem₃
      where
      lem₁ : Σ[ j ∈ _ ] (xs ++ zs ++ y ∷ ys ++ ws) ‼ i ≡ ((xs ∷ʳ y) ++ zs ++ ys ++ ws) ‼ j
      lem₁ rewrite sym (assoc (xs ∷ʳ y) zs (ys ++ ws))
                   | assoc  xs (y ∷ []) zs
                   | assoc  xs (y ∷ zs) (ys ++ ws) = forward xs zs (ys ++ ws) i

      lem₂ : Σ[ j ∈ _ ] (xs ++ zs ++ y ∷ ys ++ ws) ‼ i ≡ ((xs ∷ʳ y) ++ ys ++ zs ++ ws) ‼ j
      lem₂ with lem₁
      lem₂ | j , p with exchange″ (xs ∷ʳ y) ys zs ws j
      lem₂ | j , p | z , q = z , trans p q

      lem₃ : Σ[ j ∈ _ ] (xs ++ zs ++ y ∷ ys ++ ws) ‼ i ≡ (xs ++ y ∷ ys ++ zs ++ ws) ‼ j
      lem₃ rewrite sym (assoc xs (y ∷ ys) (zs ++ ws))
                   | sym (assoc xs (y ∷ []) ys)
                   | assoc (xs ∷ʳ y) ys (zs ++ ws) = lem₂


-- Given a list and an index which is guaranteed to be smaller than
-- the length of that list, return an index which is guaranteed to
-- return the same element (using |lookup|) from a list which has
-- duplicates removed.
contract : ∀ {a} {A : Set a} (xs ys : List A) (i : _) → Σ[ j ∈ _ ]
           (xs ++ xs ++ ys) ‼ i ≡ (xs ++ ys) ‼ j
contract      []  ys  i      = i , refl
contract (x ∷ xs) ys  zero   = zero , refl
contract (x ∷ xs) ys (suc i) with forward [] xs (xs ++ ys) i
contract (x ∷ xs) ys (suc i) | zero  , p = zero , p
contract (x ∷ xs) ys (suc i) | suc j , p with contract xs ys j
contract (x ∷ xs) ys (suc i) | suc _ , p | j , q rewrite p | q = suc j , refl


-- Given a list and an index which is guaranteed to be smaller than
-- the length of that list, return an index which is guaranteed to
-- return the same element (using |lookup|) from a list which has
-- another list prepended.
weaken : ∀ {a} {A : Set a} (xs ys : List A) (i : _) → Σ[ j ∈ _ ]
         ys ‼ i ≡ (xs ++ ys) ‼ j
weaken      []  ys i = i , refl
weaken (x ∷ xs) ys i with weaken xs ys i
weaken (x ∷ xs) ys i | j , p = suc j , p


-- Given a list, an index which is guaranteed to be smaller than the
-- length of that list, and a function, return an index which is
-- guaranteed to return the result of applying the function to element
-- (using |lookup|) from a list which has the function mapped over it.
map-lookup : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} (xs : List A) (i : _) → Σ[ j ∈ _ ]
             (f (xs ‼ i)) ≡ ((map f xs) ‼ j)
map-lookup [] ()
map-lookup (x ∷ xs) zero = zero , refl
map-lookup (x ∷ xs) (suc i) with map-lookup xs i
map-lookup (x ∷ xs) (suc i) | j , p = suc j , p
