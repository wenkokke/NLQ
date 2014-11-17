------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Algebra using (module Monoid)
open import Data.List as List using ()
open import Relation.Binary.PropositionalEquality as P using (_≡_; sym)


module Logic.Lambek.NaturalDeduction.SubsetOfLinear {ℓ} (Univ : Set ℓ) where


open import Logic.Linear.NaturalDeduction         Univ as LL
open import Logic.Linear.NaturalDeduction.Permute Univ as LLP
open import Logic.Lambek.NaturalDeduction         Univ as NL
open Monoid (List.monoid LL.Type) using (assoc)



⟦_⟧ᵀ : NL.Type → LL.Type
⟦ el A  ⟧ᵀ = el A
⟦ A ⊗ B ⟧ᵀ = ⟦ A ⟧ᵀ ⊗ ⟦ B ⟧ᵀ
⟦ A ⇐ B ⟧ᵀ = ⟦ B ⟧ᵀ ⇒ ⟦ A ⟧ᵀ
⟦ A ⇒ B ⟧ᵀ = ⟦ A ⟧ᵀ ⇒ ⟦ B ⟧ᵀ

⟦_⟧ᴬ : NL.Type → LL.List LL.Type
⟦ A ⊗ B ⟧ᴬ = ⟦ A ⟧ᴬ ++ ⟦ B ⟧ᴬ
⟦ A ⟧ᴬ     = ⟦ A ⟧ᵀ , ∅

⟦_⟧ᴶ : NL.Judgement → LL.Judgement
⟦ A ⊢ B ⟧ᴶ = ⟦ A ⟧ᴬ ⊢ ⟦ B ⟧ᵀ


id′ : ∀ A → LL ⟦ A ⊢ A ⟧ᴶ
id′ (el A)  = id
id′ (A ⊗ B) = ⊗I (id′ A) (id′ B)
id′ (A ⇐ B) = id
id′ (A ⇒ B) = id

⟦⟧ᴬ→⟦⟧ᵀ : ∀ {X A B} → LL ⟦ A ⟧ᴬ ++ X ⊢ ⟦ B ⟧ᵀ → LL ⟦ A ⟧ᵀ , X ⊢ ⟦ B ⟧ᵀ
⟦⟧ᴬ→⟦⟧ᵀ {X} {A = el A}  f = f
⟦⟧ᴬ→⟦⟧ᵀ {X} {A = A ⊗ B} {C} f = {!!}
  where
    lem₀ : LL ⟦ A ⟧ᴬ ++ ⟦ B ⟧ᴬ ++ X ⊢ ⟦ C ⟧ᵀ
    lem₀ rewrite sym (assoc (⟦ A ⟧ᴬ) (⟦ B ⟧ᴬ) X) = f
    lem₁ : LL ⟦ A ⟧ᵀ , ⟦ B ⟧ᴬ ++ X ⊢ ⟦ C ⟧ᵀ
    lem₁ = ⟦⟧ᴬ→⟦⟧ᵀ {⟦ B ⟧ᴬ ++ X} {A} {C} lem₀
    lem₂ : LL ⟦ B ⟧ᴬ ++ X ,′ ⟦ A ⟧ᵀ ⊢ ⟦ C ⟧ᵀ
    lem₂ = AX→XA lem₁
    lem₃ : LL ⟦ B ⟧ᴬ ++ (X ,′ ⟦ A ⟧ᵀ) ⊢ ⟦ C ⟧ᵀ
    lem₃ rewrite assoc (⟦ B ⟧ᴬ) X (⟦ A ⟧ᵀ , ∅) = {!lem₂!}
⟦⟧ᴬ→⟦⟧ᵀ {X} {A = A ⇐ B} f = f
⟦⟧ᴬ→⟦⟧ᵀ {X} {A = A ⇒ B} f = f


to : ∀ {A B} → NL A ⊢ B → LL ⟦ A ⊢ B ⟧ᴶ
to (id {A}) = id′ A
to (⊗I f g) = ⊗I (to f) (to g)
to (⊗E {A} {B} {C} {D} f g) = {!!}
  where
    f′ : LL ⟦ A ⟧ᴬ ⊢ ⟦ B ⟧ᵀ ⊗ ⟦ C ⟧ᵀ
    f′ = to f
    g′ : LL (⟦ B ⟧ᴬ ++ ⟦ C ⟧ᴬ) ⊢ ⟦ D ⟧ᵀ
    g′ = to g
to (⇒I f)   = {!!}
to (⇒E f g) = {!!}
to (⇐I f)   = {!!}
to (⇐E f g) = {!!}
