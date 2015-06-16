------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra                                    using (module Monoid)
open import Function                                   using (_∘_)
open import Data.List                                  using (List; _∷_; []; _++_; length)
open import Data.List.NonEmpty                         using (List⁺; _∷_; toList; head; tail)
open import Data.Nat                                   using (ℕ; suc; _≤?_)
open import Data.Fin                                   using (Fin; suc; zero; #_)
open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Nullary.Decidable                 using (True; fromWitness)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; subst; subst₂)


module Logic.Intuitionistic.Unrestricted.Lambda.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Unrestricted.Lambda.Type      Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement Univ
open Monoid (Data.List.monoid Type) using (identity; assoc)

infix 1 Λ_

data Λ_ : Judgement → Set ℓ where

  ax  : ∀ {A}
      → Λ A ∷ [] ⊢ A

  ⇒ᵢ  : ∀ {Γ₁ A B}
      → Λ A ∷ Γ₁ ⊢ B
      → Λ     Γ₁ ⊢ A ⇒ B

  ⇒ₑ  : ∀ {Γ₁ Γ₂ A B}
      → Λ Γ₁       ⊢ A ⇒ B
      → Λ       Γ₂ ⊢ A
      → Λ Γ₁ ++ Γ₂ ⊢ B

  ⊗ᵢ  : ∀ {Γ₁ Γ₂ A B}
      → Λ Γ₁       ⊢ A
      → Λ       Γ₂ ⊢ B
      → Λ Γ₁ ++ Γ₂ ⊢ A ⊗ B

  ⊗ₑ  : ∀ {Γ₁ Γ₂ A B C}
      → Λ          Γ₁        ⊢ A ⊗ B
      → Λ A ∷ B ∷        Γ₂  ⊢ C
      → Λ          Γ₁ ++ Γ₂  ⊢ C

  wᴸ₁ : ∀ {Γ₁ A B}
      → Λ     Γ₁ ⊢ B
      → Λ A ∷ Γ₁ ⊢ B

  cᴸ₁ : ∀ {Γ₁ A B}
      → Λ A ∷ A ∷ Γ₁ ⊢ B
      → Λ     A ∷ Γ₁ ⊢ B

  eᴸ  : ∀ Γ₁ Γ₂ Γ₃ Γ₄ {A}
      → Λ (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢ A
      → Λ (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢ A


-- Proof: weakening follows easily by induction from the simplified
-- version of weakening assumed above.
wᴸ  : ∀ Γ₁ {Γ₂ A}
    → Λ       Γ₂ ⊢ A
    → Λ Γ₁ ++ Γ₂ ⊢ A
wᴸ       []   f = f
wᴸ  (B ∷ Γ₁) f = wᴸ₁ (wᴸ Γ₁ f)


-- Proof: contraction of identical contexts follows easily by
-- induction from the derived rules for contaction above.
cᴸ  : ∀ (Γ₁ Γ₂ : List Type) {A}
    → Λ Γ₁ ++ Γ₁ ++ Γ₂ ⊢ A
    → Λ Γ₁       ++ Γ₂ ⊢ A
cᴸ       []   Γ₂ f = f
cᴸ  (A ∷ Γ₁) Γ₂ f = eᴸ [] (A ∷ []) Γ₁ Γ₂ (cᴸ Γ₁ (A ∷ Γ₂) lem₁)
  where
    lem₀ : Λ A ∷ (Γ₁ ++ Γ₁) ++ Γ₂ ⊢ _
    lem₀ rewrite      assoc Γ₁ Γ₁      Γ₂   = cᴸ₁ (eᴸ [] (A ∷ []) (A ∷ Γ₁) (Γ₁ ++ Γ₂) f)
    lem₁ : Λ Γ₁ ++ (Γ₁ ++ A ∷ Γ₂) ⊢ _
    lem₁ rewrite sym (assoc Γ₁ Γ₁ (A ∷ Γ₂)) = eᴸ [] (Γ₁ ++ Γ₁) (A ∷ []) Γ₂ lem₀


-- Lemma: weaker versions of eᴸ which only swap the first two
-- (or three) elements are often useful.
eᴸ₁  : ∀ {Γ A B C}
     → Λ B ∷ A ∷ Γ ⊢ C
     → Λ A ∷ B ∷ Γ ⊢ C
eᴸ₁  = eᴸ [] (_ ∷ []) (_ ∷ []) _

eᴸ₂  : ∀ {Γ A B C D}
     → Λ C ∷ A ∷ B ∷ Γ ⊢ D
     → Λ A ∷ B ∷ C ∷ Γ ⊢ D
eᴸ₂  = eᴸ [] (_ ∷ _ ∷ []) (_ ∷ []) _

eᴸ₂′ : ∀ {Γ A B C D}
     → Λ A ∷ B ∷ C ∷ Γ ⊢ D
     → Λ C ∷ A ∷ B ∷ Γ ⊢ D
eᴸ₂′ = eᴸ [] (_ ∷ []) (_ ∷ _ ∷ []) _


-- Lemma: weaker version of eᴸ and eᴿ which only swap two contexts,
-- without allowing them to be embedded in further contexts are often
-- useful as well.
sᴸ  : ∀ (Γ₁ : List Type) {Γ₂ : List Type} {A} → Λ Γ₂ ++ Γ₁ ⊢ A → Λ Γ₁ ++ Γ₂ ⊢ A
sᴸ  Γ₁ {[] } = subst  (λ Γ       → Λ       Γ   ⊢ _)                   (sym (proj₂ identity Γ₁))
sᴸ  []  {Γ₂} = subst  (λ     Γ   → Λ Γ         ⊢ _)                                             (proj₂ identity Γ₂)
sᴸ  Γ₁ {Γ₂} = subst₂ (λ Γ₁′ Γ₂′ → Λ Γ₂ ++ Γ₁′ ⊢ _ → Λ Γ₁ ++ Γ₂′ ⊢ _) (     proj₂ identity Γ₁ ) (proj₂ identity Γ₂) (eᴸ  [] Γ₁ Γ₂ [])


-- Lemma: introduction and elimination of right-handed empty context.
[]ᵢ : ∀ {Γ A} → Λ Γ      ⊢ A → Λ Γ ++ [] ⊢ A
[]ᵢ {Γ} f rewrite proj₂ identity Γ = f
[]ₑ : ∀ {Γ A} → Λ Γ ++ [] ⊢ A → Λ Γ      ⊢ A
[]ₑ {Γ} f rewrite proj₂ identity Γ = f


-- Lemma: cut.
cut′ : ∀ {Γ Δ A B} → Λ Γ ⊢ A → Λ A ∷ Δ ⊢ B → Λ Γ ++ Δ ⊢ B
cut′ {Γ} f g = sᴸ Γ (⇒ₑ (⇒ᵢ g) f)


private

  swapList1 : ∀ {ℓ} {A : Set ℓ} (x : A) (xs : List A) (i : Fin (length xs)) → List⁺ A
  swapList1 x [] ()
  swapList1 x (y ∷ xs)  zero   = y ∷ (x ∷ xs)
  swapList1 x (y ∷ xs) (suc i) with swapList1 x xs i
  swapList1 x (y ∷ xs) (suc i) | (z ∷ zs) = z ∷ (y ∷ zs)

  swapList : ∀ {ℓ} {A : Set ℓ} (xs : List A) (i j : Fin (length xs)) → List A
  swapList [] () ()
  swapList (x ∷ xs)  zero    zero   = x ∷ xs
  swapList (x ∷ xs)  zero   (suc j) with swapList1 x xs j
  swapList (x ∷ xs)  zero   (suc j) | (y ∷ ys) = (y ∷ ys)
  swapList (x ∷ xs) (suc i)  zero   with swapList1 x xs i
  swapList (x ∷ xs) (suc i)  zero   | (y ∷ ys) = (y ∷ ys)
  swapList (x ∷ xs) (suc i) (suc j) = x ∷ (swapList xs i j)

  swapCtxt1 : ∀ {Γ B} (A : Type) (i : Fin (length Γ)) → Λ A ∷ Γ ⊢ B → Λ toList (swapList1 A Γ i) ⊢ B
  swapCtxt1 {[]} _ ()
  swapCtxt1 {C ∷ Γ} A  zero   f = eᴸ₁ f
  swapCtxt1 {C ∷ Γ} A (suc i) f = eᴸ₁ (sᴸ (C ∷ []) (⇒ₑ (swapCtxt1 {Γ} A i (⇒ᵢ (eᴸ₁ f))) ax))

  swapCtxt : ∀ {Γ B} (i j : Fin (length Γ)) →  Λ Γ ⊢ B → Λ swapList Γ i j ⊢ B
  swapCtxt {[]} () ()
  swapCtxt {A ∷ Γ}  zero    zero   f = f
  swapCtxt {A ∷ Γ}  zero   (suc j) f = swapCtxt1 {Γ} A j f
  swapCtxt {A ∷ Γ} (suc i)  zero   f = swapCtxt1 {Γ} A i f
  swapCtxt {A ∷ Γ} (suc i) (suc j) f = sᴸ (A ∷ []) (⇒ₑ (swapCtxt {Γ} i j (⇒ᵢ f)) ax)


eᵢⱼ : ∀ {Γ B} (m n : ℕ)
       {m∈Γ : True (suc m ≤? length Γ)}
       {n∈Γ : True (suc n ≤? length Γ)}
         → Λ Γ ⊢ B → Λ swapList Γ (#_ m {m<n = m∈Γ}) (#_ n {m<n = n∈Γ}) ⊢ B
eᵢⱼ m n {m∈Γ} {n∈Γ} f = swapCtxt (#_ m {m<n = m∈Γ}) (#_ n {m<n = n∈Γ}) f


-- Several pre-computed exchanges (which won't use any computational rules)
e₀₁ : ∀ {A B C Γ} → Λ B ∷ (A ∷ Γ) ⊢ C → Λ A ∷ (B ∷ Γ) ⊢ C
e₀₁ f = eᴸ [] (_ ∷ []) (_ ∷ []) _ f
e₁₂ : ∀ {A B C D Γ} → Λ A ∷ (C ∷ (B ∷ Γ)) ⊢ D → Λ A ∷ (B ∷ (C ∷ Γ)) ⊢ D
e₁₂ f = eᴸ (_ ∷ []) (_ ∷ []) (_ ∷ []) _ f
e₀₂ : ∀ {A B C D Γ} → Λ C ∷ (B ∷ (A ∷ Γ)) ⊢ D → Λ A ∷ (B ∷ (C ∷ Γ)) ⊢ D
e₀₂ f = e₀₁ (e₁₂ (e₀₁ f))
e₂₃ : ∀ {A B C D E Γ} → Λ A ∷ (B ∷ (D ∷ (C ∷ Γ))) ⊢ E → Λ A ∷ (B ∷ (C ∷ (D ∷ Γ))) ⊢ E
e₂₃ f = eᴸ (_ ∷ (_ ∷ [])) (_ ∷ []) (_ ∷ []) _ f
e₁₃ : ∀ {A B C D E Γ} → Λ A ∷ (D ∷ (C ∷ (B ∷ Γ))) ⊢ E → Λ A ∷ (B ∷ (C ∷ (D ∷ Γ))) ⊢ E
e₁₃ f = e₁₂ (e₂₃ (e₁₂ f))
e₀₃ : ∀ {A B C D E Γ}  → Λ D ∷ (B ∷ (C ∷ (A ∷ Γ))) ⊢ E → Λ A ∷ (B ∷ (C ∷ (D ∷ Γ))) ⊢ E
e₀₃ f = e₀₁ (e₁₂ (e₂₃ (e₁₂ (e₀₁ f))))
