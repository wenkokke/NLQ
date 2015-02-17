------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Algebra                                         using (module Monoid)
open import Data.List                                       using (List; _++_) renaming ([] to ∅; _∷_ to _,_; _∷ʳ_ to _,′_)
open import Data.Product                                    using (proj₁; proj₂)
open import Relation.Nullary                                using (Dec)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)


-- A quick overview of the functions implemented in this module:
--
--   ∅ᵢ          : X , ∅ ⊢ A → LL X ⊢ A
--   ∅ₑ          : X ⊢ A → LL X , ∅ ⊢ A
--
--   AX→XA       : A , X ⊢ B → X , A ⊢ B
--   XA→AX       : X , A ⊢ B → A , X ⊢ B
--
--   YX→XY       : Y , X ⊢ A → X , Y ⊢ A
--
--   Y[XZ]→X[YZ] : Y , (X , Z) ⊢ A → X , (Y , Z) ⊢ A
--   [YX]Z→[XY]Z : (Y , X) , Z ⊢ A → (X , Y) , Z ⊢ A
--   [XZ]Y→[XY]Z : (X , Z) , Y ⊢ A → (X , Y) , Z ⊢ A
--   X[ZY]→X[YZ] : X , (Z , Y) ⊢ A → X , (Y , Z) ⊢ A
--
--   XYZW→XWZY   : (X , Y) , (Z , W) ⊢ A → (X , W) , (Z , Y) ⊢ A
--   XYZW→YWXZ   : (X , Y) , (Z , W) ⊢ A → (Y , W) , (X , Z) ⊢ A
--   XYZW→ZXWY   : (X , Y) , (Z , W) ⊢ A → (Z , X) , (W , Y) ⊢ A
--   XYZW→ZYXW   : (X , Y) , (Z , W) ⊢ A → (Z , Y) , (X , W) ⊢ A
--
--   ABX→A⊗BX    : A , B , X ⊢ C → A ⊗ B , X ⊢ C
--   XAB→XA⊗B    : X , A , B ⊢ C → X , A ⊗ B ⊢ C
--


module Logic.Intuitionistic.Unrestricted.Lambda.Permute {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Unrestricted.Lambda.Type      Univ as T
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement Univ as J
open import Logic.Intuitionistic.Unrestricted.Lambda.Base      Univ as B
open Monoid (Data.List.monoid Type) using (identity; assoc)



AX→XA : ∀ {X A B} → Λ A , X ⊢ B → Λ X ,′ A ⊢ B
AX→XA {X} {A} {B} t = lem1 lem2
  where
    lem1 : Λ A , (X ++ ∅) ⊢ B → Λ X ,′ A ⊢ B
    lem1 = eᴸ ∅ X (A , ∅) ∅
    lem2 : Λ A , (X ++ ∅) ⊢ B
    lem2 rewrite proj₂ identity X = t


XA→AX : ∀ {X A B} → Λ X ,′ A ⊢ B → Λ A , X ⊢ B
XA→AX {X} {A} {B} t = lem2
  where
    lem1 : Λ A , X ++ ∅ ⊢ B
    lem1 = eᴸ ∅ (A , ∅) X ∅ t
    lem2 : Λ A , X ⊢ B
    lem2 rewrite sym (proj₂ identity (A , X)) = lem1


YX→XY : ∀ {A} X Y → Λ Y ++ X ⊢ A → Λ X ++ Y ⊢ A
YX→XY {A} X Y t = lem₃
  where
    lem₁ : Λ Y ++ X ++ ∅ ⊢ A
    lem₁ rewrite proj₂ identity X = t
    lem₂ : Λ X ++ Y ++ ∅ ⊢ A
    lem₂ = eᴸ ∅ X Y ∅ lem₁
    lem₃ : Λ X ++ Y ⊢ A
    lem₃ = PropEq.subst (λ Y → Λ X ++ Y ⊢ A) (proj₂ identity Y) lem₂


Y[XZ]→X[YZ] : ∀ {A} X Y Z → Λ Y ++ (X ++ Z) ⊢ A → Λ X ++ (Y ++ Z) ⊢ A
Y[XZ]→X[YZ] {A} X Y Z t = eᴸ ∅ X Y Z t


[YX]Z→[XY]Z : ∀ {A} X Y Z → Λ (Y ++ X) ++ Z ⊢ A → Λ (X ++ Y) ++ Z ⊢ A
[YX]Z→[XY]Z {A} X Y Z t = lem₃
  where
    lem₁ : Λ Y ++ (X ++ Z) ⊢ A
    lem₁ rewrite sym (assoc Y X Z) = t
    lem₂ : Λ X ++ (Y ++ Z) ⊢ A
    lem₂ = Y[XZ]→X[YZ] X Y Z lem₁
    lem₃ : Λ (X ++ Y) ++ Z ⊢ A
    lem₃ rewrite assoc X Y Z = lem₂


[XZ]Y→[XY]Z : ∀ {A} X Y Z → Λ (X ++ Z) ++ Y ⊢ A → Λ (X ++ Y) ++ Z ⊢ A
[XZ]Y→[XY]Z {A} X Y Z t = lem₃
  where
    lem₁ : Λ (X ++ Z) ++ Y ++ ∅ ⊢ A
    lem₁ rewrite proj₂ identity Y = t
    lem₂ : Λ (X ++ Y) ++ Z ++ ∅ ⊢ A
    lem₂ = eᴸ X Y Z ∅ lem₁
    lem₃ : Λ (X ++ Y) ++ Z ⊢ A
    lem₃ = PropEq.subst (λ Z → Λ (X ++ Y) ++ Z ⊢ A) (proj₂ identity Z) lem₂


X[ZY]→X[YZ] : ∀ {A} X Y Z → Λ X ++ (Z ++ Y) ⊢ A → Λ X ++ (Y ++ Z) ⊢ A
X[ZY]→X[YZ] {A} X Y Z t = lem₃
  where
    lem₁ : Λ (X ++ Z) ++ Y ⊢ A
    lem₁ rewrite assoc X Z Y = t
    lem₂ : Λ (X ++ Y) ++ Z ⊢ A
    lem₂ = [XZ]Y→[XY]Z X Y Z lem₁
    lem₃ : Λ X ++ Y ++ Z ⊢ A
    lem₃ rewrite sym (assoc X Y Z) = lem₂


XYZW→XWZY : ∀ {A} X Y Z W → Λ (X ++ Y) ++ (Z ++ W) ⊢ A → Λ (X ++ W) ++ (Z ++ Y) ⊢ A
XYZW→XWZY {A} X Y Z W t = lem₃
  where
    lem₁ : Λ (X ++ Y) ++ (W ++ Z) ⊢ A
    lem₁ = X[ZY]→X[YZ] (X ++ Y) W Z t
    lem₂ : Λ (X ++ W) ++ (Y ++ Z) ⊢ A
    lem₂ = eᴸ X W Y Z lem₁
    lem₃ : Λ (X ++ W) ++ (Z ++ Y) ⊢ A
    lem₃ = X[ZY]→X[YZ] (X ++ W) Z Y lem₂


XYZW→YWXZ : ∀ {A} X Y Z W → Λ (X ++ Y) ++ (Z ++ W) ⊢ A → Λ (Y ++ W) ++ (X ++ Z) ⊢ A
XYZW→YWXZ {A} X Y Z W t = lem₃
  where
    lem₁ : Λ (Y ++ X) ++ (Z ++ W) ⊢ A
    lem₁ = [YX]Z→[XY]Z Y X (Z ++ W) t
    lem₂ : Λ (Y ++ X) ++ (W ++ Z) ⊢ A
    lem₂ = X[ZY]→X[YZ] (Y ++ X) W Z lem₁
    lem₃ : Λ (Y ++ W) ++ (X ++ Z) ⊢ A
    lem₃ = eᴸ Y W X Z lem₂


XYZW→ZXWY : ∀ {A} X Y Z W → Λ (X ++ Y) ++ (Z ++ W) ⊢ A → Λ (Z ++ X) ++ (W ++ Y) ⊢ A
XYZW→ZXWY {A} X Y Z W t = lem₃
  where
    lem₁ : Λ (X ++ Z) ++ (Y ++ W) ⊢ A
    lem₁ = eᴸ X Z Y W t
    lem₂ : Λ (Z ++ X) ++ (Y ++ W) ⊢ A
    lem₂ = [YX]Z→[XY]Z Z X (Y ++ W) lem₁
    lem₃ : Λ (Z ++ X) ++ (W ++ Y) ⊢ A
    lem₃ = X[ZY]→X[YZ] (Z ++ X) W Y lem₂


XYZW→ZYXW : ∀ {A} X Y Z W → Λ (X ++ Y) ++ (Z ++ W) ⊢ A → Λ (Z ++ Y) ++ (X ++ W) ⊢ A
XYZW→ZYXW {A} X Y Z W t = lem₃
  where
    lem₁ : Λ (Y ++ X) ++ (Z ++ W) ⊢ A
    lem₁ = [YX]Z→[XY]Z Y X (Z ++ W) t
    lem₂ : Λ (Y ++ Z) ++ (X ++ W) ⊢ A
    lem₂ = eᴸ Y Z X W lem₁
    lem₃ : Λ (Z ++ Y) ++ (X ++ W) ⊢ A
    lem₃ = [YX]Z→[XY]Z Z Y (X ++ W) lem₂


ABX→A⊗BX : ∀ {X A B C} → Λ A , B , X ⊢ C → Λ A ⊗ B , X ⊢ C
ABX→A⊗BX t = ⊗ₑ ax t


XAB→XA⊗B : ∀ {X A B C} → Λ X ++ (A , B , ∅) ⊢ C → Λ X ,′ A ⊗ B ⊢ C
XAB→XA⊗B {X} {A} {B} {C} = lem₃
  where
    lem₁ : Λ X ,′ A ,′ B ⊢ C → Λ X ,′ A ⊗ B ⊢ C
    lem₁ t = AX→XA (ABX→A⊗BX (XA→AX {B , X} {A} (XA→AX {X ,′ A} {B} t)))
    lem₂ : ∀ {a} {A : Set a} xs (y z : A) → xs ,′ y ,′ z  ≡ xs ++ (y , z , ∅)
    lem₂ ∅ y z = refl
    lem₂ (x , xs) y z = cong (_,_ x) (lem₂ xs y z)
    lem₃ : Λ X ++ (A , B , ∅) ⊢ C → Λ X ,′ A ⊗ B ⊢ C
    lem₃ rewrite sym (lem₂ X A B) = lem₁
