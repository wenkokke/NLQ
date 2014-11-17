------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


module Logic.Linear.LambekVanBenthem.EquivalentToNaturalDeduction {ℓ} (Univ : Set ℓ) where


open import Logic.Linear.Type                       Univ as T
open import Logic.Linear.LambekVanBenthem.Judgement Univ as LPJ
open import Logic.Linear.LambekVanBenthem.Base      Univ as LPB
open import Logic.Linear.NaturalDeduction.Judgement Univ as NDJ
open import Logic.Linear.NaturalDeduction.Structure Univ as NDS
open import Logic.Linear.NaturalDeduction.Base      Univ as NDB
open import Logic.Linear.NaturalDeduction.Permute   Univ as NDP





to : ∀ {A B} → LP A ⊢ B → LL A , ∅ ⊢ B
to id         = id
to (⇒I {X} {A} {B} f) = {!to (comm f)!}
to (⇒E f₁ f₂) = {!!}
to (⊗I f₁ f₂) = ⊗E id (⊗I (to f₁) (to f₂))
to (⊗E f₁ f₂) = ⇒E (⇒I (to f₂)) (to f₁)
to (assᴸ f)   = {!!}
to (assᴿ f)   = {!!}
to (comm f)   = {!!}
