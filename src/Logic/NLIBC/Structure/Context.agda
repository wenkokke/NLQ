------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level                                 using ()
open import Category.Functor                      using (module RawFunctor; RawFunctor)
open import Data.Nat                              using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties.Simple as ℕ       using ()
open import Data.Fin                              using (Fin; suc; zero)
open import Data.Maybe                            using (Maybe; just; nothing)
open import Data.Product                          using (_×_; _,_; proj₁; proj₂)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans; cong; refl)


module Logic.NLIBC.Structure.Context {ℓ} (Atom : Set ℓ) where


open import Logic.NLIBC.Structure Atom


infixr 5 _∙>_
infixl 5 _<∙_
infixr 5 _∘>_
infixl 5 _<∘_

record Composable (C : Set ℓ) : Set ℓ where
  infixl 50 _<_>
  field
    _<_>   : C → C → C

record Pluggable (C A : Set ℓ) : Set ℓ where
  infixl 40 _[_]
  field
    _[_]       : C → A → A
    composable : Composable C

  open Composable composable using (_<_>)

  field
    <>-def     : ∀ Γ Δ x → (Γ [ Δ [ x ] ]) ≡ (Γ < Δ > [ x ])


data Context : Set ℓ where
  []    : Context
  _∙>_  : Structure → Context   → Context
  _<∙_  : Context   → Structure → Context
  _∘>_  : Structure → Context   → Context
  _<∘_  : Context   → Structure → Context


instance
  composable : Composable Context
  composable = record { _<_> = _<_> }
    where
      _<_> : Context → Context → Context
      []       < Δ > = Δ
      (q ∙> Γ) < Δ > = q ∙> (Γ < Δ >)
      (Γ <∙ q) < Δ > = (Γ < Δ >) <∙ q
      (q ∘> Γ) < Δ > = q ∘> (Γ < Δ >)
      (Γ <∘ q) < Δ > = (Γ < Δ >) <∘ q

  pluggable : Pluggable Context Structure
  pluggable = record { _[_] = _[_] ; composable = composable ; <>-def = <>-def }
    where
    _[_] : Context → Structure → Structure
    []        [ Δ ] = Δ
    (Γ ∙> Γ′) [ Δ ] = Γ ∙ (Γ′ [ Δ ])
    (Γ <∙ Γ′) [ Δ ] = (Γ [ Δ ]) ∙ Γ′
    (Γ ∘> Γ′) [ Δ ] = Γ ∘ (Γ′ [ Δ ])
    (Γ <∘ Γ′) [ Δ ] = (Γ [ Δ ]) ∘ Γ′

    open Composable composable using (_<_>)

    <>-def : ∀ Γ Δ p → (Γ [ Δ [ p ] ]) ≡ ((Γ < Δ >) [ p ])
    <>-def    []    Δ p = refl
    <>-def (_ ∙> Γ) Δ p rewrite <>-def Γ Δ p = refl
    <>-def (Γ <∙ _) Δ p rewrite <>-def Γ Δ p = refl
    <>-def (_ ∘> Γ) Δ p rewrite <>-def Γ Δ p = refl
    <>-def (Γ <∘ _) Δ p rewrite <>-def Γ Δ p = refl


data Context₁ : Set ℓ where
  []    : Context₁
  _∙>_  : Structure → Context₁  → Context₁
  _<∙_  : Context₁  → Structure → Context₁


instance
  composable₁ : Composable Context₁
  composable₁ = record { _<_> = _<_> }
    where
    _<_> : Context₁ → Context₁ → Context₁
    []       < Δ > = Δ
    (q ∙> Γ) < Δ > = q ∙> (Γ < Δ >)
    (Γ <∙ q) < Δ > = (Γ < Δ >) <∙ q

  pluggable₁ : Pluggable Context₁ Structure
  pluggable₁ = record { _[_] = _[_] ; composable = composable₁ ; <>-def = <>-def}
    where
    _[_] : Context₁ → Structure → Structure
    []        [ Δ ] = Δ
    (Γ ∙> Γ′) [ Δ ] = Γ ∙ (Γ′ [ Δ ])
    (Γ <∙ Γ′) [ Δ ] = (Γ [ Δ ]) ∙ Γ′

    open Composable composable₁ using (_<_>)

    <>-def : ∀ Γ Δ p → (Γ [ Δ [ p ] ]) ≡ ((Γ < Δ >) [ p ])
    <>-def    []    Δ p = refl
    <>-def (_ ∙> Γ) Δ p rewrite <>-def Γ Δ p = refl
    <>-def (Γ <∙ _) Δ p rewrite <>-def Γ Δ p = refl


open Composable {{...}} public using (_<_>)
open Pluggable  {{...}} public using (_[_]; <>-def)


λx_[x] : (Γ : Context₁) → Structure
λx   []   [x] = I
λx p ∙> Γ [x] = (B ∙ p) ∙ λx Γ [x]
λx Γ <∙ r [x] = (C ∙ λx Γ [x]) ∙ r




-- HERE BE DRAGONS
--
-- The code below isn't really used, but it's a work-in-progress
-- version of linear contexts. Yes, I'm well aware this shouldn't be
-- in 'master', but it's my project and only I am working on it.
--
-- TODO: move experimental code into separate branch
{-

data Contextᵢ : ℕ → Set ℓ where
  var : Contextᵢ 1
  con : Structure → Contextᵢ 0
  dot : ∀ {m n m+n} (pr : m+n ≡ m + n) → Contextᵢ m → Contextᵢ n → Contextᵢ m+n


private
  break : ∀ {m n} (i : Fin (m + n)) → Fin m ⊎ Fin n
  break {zero}   i = inj₂ i
  break {suc m}  zero = inj₁ zero
  break {suc m} (suc i) with break i
  break {suc m} (suc i) | inj₁ j = inj₁ (suc j)
  break {suc m} (suc i) | inj₂ j = inj₂ j


_[_]ᵢ_ : ∀ {n} → Contextᵢ (suc n) → Structure → Fin (suc n) → Contextᵢ n
Γ [ Δ ]ᵢ i = sub i Γ Δ
  where
  sub : ∀ {n} (i : Fin (suc n)) (Γ : Contextᵢ (suc n)) (p : Structure) → Contextᵢ n
  sub zero var p = con p
  sub (suc ()) var p
  sub i (dot {zero}  {zero} () l r) p
  sub i (dot {zero}  {suc n} refl l r) p
    = dot refl l (sub i r p)
  sub i (dot {suc m} {zero}  refl l r) p
    rewrite (ℕ.+-right-identity m)
    = dot (sym (ℕ.+-right-identity m)) (sub i l p) r
  sub i (dot {suc m} {suc n} refl l r) p
    with break {suc m} {suc n} i
  ... | inj₁ j = dot refl (sub j l p) r
  ... | inj₂ j = dot (ℕ.+-suc m n) l (sub j r p)


⌊_⌋₀ : Contextᵢ 0 → Structure
⌊ con Γ ⌋₀ = Γ
⌊ dot {zero}  {zero}  pr l r ⌋₀ = ⌊ l ⌋₀ ∙ ⌊ r ⌋₀
⌊ dot {zero}  {suc _} () l r ⌋₀
⌊ dot {suc _} {zero}  () l r ⌋₀
⌊ dot {suc _} {suc _} () l r ⌋₀


⌊_⌋₁ : Contextᵢ 1 → Context₁
⌊ var ⌋₁ = []
⌊ dot {zero}        {zero}        () _ _ ⌋₁
⌊ dot {zero}        {suc zero}    pr l r ⌋₁ = ⌊ l ⌋₀ ∙> ⌊ r ⌋₁
⌊ dot {zero}        {suc (suc _)} () _ _ ⌋₁
⌊ dot {suc zero}    {zero}        pr l r ⌋₁ = ⌊ l ⌋₁ <∙ ⌊ r ⌋₀
⌊ dot {suc (suc _)} {zero}        () _ _ ⌋₁
⌊ dot {suc m}       {suc n}       pr _ _ ⌋₁
  with trans pr (cong suc (ℕ.+-suc m n)) ; ... | ()


_[_]₂_ : Contextᵢ 2 → Structure → Fin 2 → Context₁
Γ [ Δ ]₂ i = ⌊ Γ [ Δ ]ᵢ i ⌋₁

-- -}
-- -}
-- -}
-- -}
-- -}
