------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Algebra using (module Monoid)
open import Data.List as List using ()
open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; cong; sym)


-- A quick overview of the functions implemented in this module:
--
--   X∅→X        : X , ∅ ⊢ A → LL X ⊢ A
--   X→X∅        : X ⊢ A → LL X , ∅ ⊢ A
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


module Logic.Linear.NaturalDeduction.Permute {ℓ} (Univ : Set ℓ) where


open import Logic.Linear.Type                       Univ as T
open import Logic.Linear.NaturalDeduction.Structure Univ as NDS
open import Logic.Linear.NaturalDeduction.Judgement Univ as NDJ
open import Logic.Linear.NaturalDeduction.Base      Univ as NDB
open Monoid (List.monoid Type) using (identity; assoc)


X∅→X : ∀ {X A} → LL X ++ ∅ ⊢ A → LL X ⊢ A
X∅→X {X} f rewrite proj₂ identity X = f


X→X∅ : ∀ {X A} → LL X ⊢ A → LL X ++ ∅ ⊢ A
X→X∅ {X} f rewrite proj₂ identity X = f


AX→XA : ∀ {X A B} → LL A , X ⊢ B → LL X ,′ A ⊢ B
AX→XA {X} {A} {B} t = lem1 lem2
  where
    lem1 : LL A , (X ++ ∅) ⊢ B → LL X ,′ A ⊢ B
    lem1 = exch {∅} {X} {A , ∅} {∅}
    lem2 : LL A , (X ++ ∅) ⊢ B
    lem2 rewrite proj₂ identity X = t


XA→AX : ∀ {X A B} → LL X ,′ A ⊢ B → LL A , X ⊢ B
XA→AX {X} {A} {B} t = lem2
  where
    lem1 : LL A , X ++ ∅ ⊢ B
    lem1 = exch {∅} {A , ∅} {X} {∅} t
    lem2 : LL A , X ⊢ B
    lem2 rewrite sym (proj₂ identity (A , X)) = lem1


YX→XY : ∀ {A} X Y → LL Y ++ X ⊢ A → LL X ++ Y ⊢ A
YX→XY {A} X Y t = lem₃
  where
    lem₁ : LL Y ++ X ++ ∅ ⊢ A
    lem₁ rewrite proj₂ identity X = t
    lem₂ : LL X ++ Y ++ ∅ ⊢ A
    lem₂ = exch {∅} {X} {Y} {∅} lem₁
    lem₃ : LL X ++ Y ⊢ A
    lem₃ = PropEq.subst (λ Y → LL X ++ Y ⊢ A) (proj₂ identity Y) lem₂


Y[XZ]→X[YZ] : ∀ {A} X Y Z → LL Y ++ (X ++ Z) ⊢ A → LL X ++ (Y ++ Z) ⊢ A
Y[XZ]→X[YZ] {A} X Y Z t = exch {∅} {X} {Y} {Z} t


[YX]Z→[XY]Z : ∀ {A} X Y Z → LL (Y ++ X) ++ Z ⊢ A → LL (X ++ Y) ++ Z ⊢ A
[YX]Z→[XY]Z {A} X Y Z t = lem₃
  where
    lem₁ : LL Y ++ (X ++ Z) ⊢ A
    lem₁ rewrite sym (assoc Y X Z) = t
    lem₂ : LL X ++ (Y ++ Z) ⊢ A
    lem₂ = Y[XZ]→X[YZ] X Y Z lem₁
    lem₃ : LL (X ++ Y) ++ Z ⊢ A
    lem₃ rewrite assoc X Y Z = lem₂


[XZ]Y→[XY]Z : ∀ {A} X Y Z → LL (X ++ Z) ++ Y ⊢ A → LL (X ++ Y) ++ Z ⊢ A
[XZ]Y→[XY]Z {A} X Y Z t = lem₃
  where
    lem₁ : LL (X ++ Z) ++ Y ++ ∅ ⊢ A
    lem₁ rewrite proj₂ identity Y = t
    lem₂ : LL (X ++ Y) ++ Z ++ ∅ ⊢ A
    lem₂ = exch {X} {Y} {Z} {∅} lem₁
    lem₃ : LL (X ++ Y) ++ Z ⊢ A
    lem₃ = PropEq.subst (λ Z → LL (X ++ Y) ++ Z ⊢ A) (proj₂ identity Z) lem₂


X[ZY]→X[YZ] : ∀ {A} X Y Z → LL X ++ (Z ++ Y) ⊢ A → LL X ++ (Y ++ Z) ⊢ A
X[ZY]→X[YZ] {A} X Y Z t = lem₃
  where
    lem₁ : LL (X ++ Z) ++ Y ⊢ A
    lem₁ rewrite assoc X Z Y = t
    lem₂ : LL (X ++ Y) ++ Z ⊢ A
    lem₂ = [XZ]Y→[XY]Z X Y Z lem₁
    lem₃ : LL X ++ Y ++ Z ⊢ A
    lem₃ rewrite sym (assoc X Y Z) = lem₂


XYZW→XWZY : ∀ {A} X Y Z W → LL (X ++ Y) ++ (Z ++ W) ⊢ A → LL (X ++ W) ++ (Z ++ Y) ⊢ A
XYZW→XWZY {A} X Y Z W t = lem₃
  where
    lem₁ : LL (X ++ Y) ++ (W ++ Z) ⊢ A
    lem₁ = X[ZY]→X[YZ] (X ++ Y) W Z t
    lem₂ : LL (X ++ W) ++ (Y ++ Z) ⊢ A
    lem₂ = exch {X} {W} {Y} {Z} lem₁
    lem₃ : LL (X ++ W) ++ (Z ++ Y) ⊢ A
    lem₃ = X[ZY]→X[YZ] (X ++ W) Z Y lem₂


XYZW→YWXZ : ∀ {A} X Y Z W → LL (X ++ Y) ++ (Z ++ W) ⊢ A → LL (Y ++ W) ++ (X ++ Z) ⊢ A
XYZW→YWXZ {A} X Y Z W t = lem₃
  where
    lem₁ : LL (Y ++ X) ++ (Z ++ W) ⊢ A
    lem₁ = [YX]Z→[XY]Z Y X (Z ++ W) t
    lem₂ : LL (Y ++ X) ++ (W ++ Z) ⊢ A
    lem₂ = X[ZY]→X[YZ] (Y ++ X) W Z lem₁
    lem₃ : LL (Y ++ W) ++ (X ++ Z) ⊢ A
    lem₃ = exch {Y} {W} {X} {Z} lem₂


XYZW→ZXWY : ∀ {A} X Y Z W → LL (X ++ Y) ++ (Z ++ W) ⊢ A → LL (Z ++ X) ++ (W ++ Y) ⊢ A
XYZW→ZXWY {A} X Y Z W t = lem₃
  where
    lem₁ : LL (X ++ Z) ++ (Y ++ W) ⊢ A
    lem₁ = exch {X} {Z} {Y} {W} t
    lem₂ : LL (Z ++ X) ++ (Y ++ W) ⊢ A
    lem₂ = [YX]Z→[XY]Z Z X (Y ++ W) lem₁
    lem₃ : LL (Z ++ X) ++ (W ++ Y) ⊢ A
    lem₃ = X[ZY]→X[YZ] (Z ++ X) W Y lem₂


XYZW→ZYXW : ∀ {A} X Y Z W → LL (X ++ Y) ++ (Z ++ W) ⊢ A → LL (Z ++ Y) ++ (X ++ W) ⊢ A
XYZW→ZYXW {A} X Y Z W t = lem₃
  where
    lem₁ : LL (Y ++ X) ++ (Z ++ W) ⊢ A
    lem₁ = [YX]Z→[XY]Z Y X (Z ++ W) t
    lem₂ : LL (Y ++ Z) ++ (X ++ W) ⊢ A
    lem₂ = exch {Y} {Z} {X} {W} lem₁
    lem₃ : LL (Z ++ Y) ++ (X ++ W) ⊢ A
    lem₃ = [YX]Z→[XY]Z Z Y (X ++ W) lem₂


ABX→A⊗BX : ∀ {X A B C} → LL A , B , X ⊢ C → LL A ⊗ B , X ⊢ C
ABX→A⊗BX t = ⊗E id t


XAB→XA⊗B : ∀ {X A B C} → LL X ++ (A , B , ∅) ⊢ C → LL X ,′ A ⊗ B ⊢ C
XAB→XA⊗B {X} {A} {B} {C} = lem₃
  where
    lem₁ : LL X ,′ A ,′ B ⊢ C → LL X ,′ A ⊗ B ⊢ C
    lem₁ t = AX→XA (ABX→A⊗BX (XA→AX {B , X} {A} (XA→AX {X ,′ A} {B} t)))
    lem₂ : ∀ {a} {A : Set a} xs (y z : A) → xs ,′ y ,′ z  ≡ xs ++ (y , z , ∅)
    lem₂ ∅ y z = refl
    lem₂ (x , xs) y z = cong (_,_ x) (lem₂ xs y z)
    lem₃ : LL X ++ (A , B , ∅) ⊢ C → LL X ,′ A ⊗ B ⊢ C
    lem₃ rewrite sym (lem₂ X A B) = lem₁
