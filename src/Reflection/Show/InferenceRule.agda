------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function           using (_∘_)
open import Category.Monad     using (module RawMonad)
open import Data.Bool          using (Bool; true; false; not; if_then_else_; _∧_)
open import Data.Char          using (Char) renaming (_==_ to _C==_)
open import Data.List          using (List; _∷_; []; filter; drop; break; intersperse; foldr; all)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; _∷ʳ′_; snocView)
open import Data.Maybe         using (Maybe; just; nothing; is-nothing)
open import Data.Nat           using (ℕ; zero; suc; _⊔_)
open import Data.String        using (String; toList; fromList; _++_) renaming (_==_ to _S==_)
open import Data.Product       using (_×_; _,_)
open import Reflection
open import Logic.NLIBC ℕ using (⇨ᴸ)


module Reflection.Show.InferenceRule (isBanned : Name → Bool) where


open RawMonad {{...}} using (_<$>_)
instance
  monadList  = Data.List.monad
  monadMaybe = Data.Maybe.monad


private
  unqualifiedName : Name → String
  unqualifiedName n =
    fromList (unqualifiedName′ (toList (showName n)))
    where
      lastIndex : ℕ → Char → List Char → ℕ
      lastIndex i x      []  = 0
      lastIndex i x (y ∷ ys) =
        if x C== y
          then i ⊔ lastIndex (suc i) x ys
          else     lastIndex (suc i) x ys

      unqualifiedName′ : List Char → List Char
      unqualifiedName′ n =  drop (suc (lastIndex 0 '.' n)) n


  {-# TERMINATING #-}
  showOp :  (f : String → String) (op : String) (xs : List String) → String
  showOp f op xs = showOp′ f (toList op) xs
    where
    showOp′ : (f : String → String) (op : List Char) (xs : List String) → String
    showOp′ f        []       xs  = foldr _++_ "" (intersperse " " xs)
    showOp′ f ('_' ∷ op)      []  = fromList ('_' ∷ op)
    showOp′ f ('_' ∷ op) (x ∷ xs) = x ++ showOp′ f op xs
    showOp′ f        op       xs  with break (_C== '_') op
    showOp′ f        op       xs  | (op₁ , op₂) = f (fromList op₁) ++ showOp′ f op₂ xs


  lookupVar : ℕ → List String → String
  lookupVar n       []      = ""
  lookupVar zero    (x ∷ _) = x
  lookupVar (suc n) (_ ∷ e) = lookupVar n e


  agdaVar = λ r → "\\AgdaBound{" ++ r ++ "}\\;"
  agdaCon = λ r → "\\AgdaInductiveConstructor{" ++ r ++ "}\\;"
  agdaDef = λ r → "\\AgdaFunction{" ++ r ++ "}\\;"


  {-# TERMINATING #-}
  mutual
    isAllowed : Arg Term → Bool
    isAllowed (arg i t) = isVisible i ∧ not (isBanned′ t)
      where
      isBanned′ : Term → Bool
      isBanned′ (con c _) = isBanned c
      isBanned′ (def f _) = isBanned f
      isBanned′        _  = false
      isVisible : Arg-info → Bool
      isVisible (arg-info visible _) = true
      isVisible (arg-info _       _) = false

    showArg : (e : List String) (t : Arg Term) → String
    showArg e (arg _ t) = showTerm e t

    showTerm : (e : List String) (t : Term) → String
    showTerm e (var x args) = showOp agdaVar (lookupVar x e)     (showArg e <$> filter isAllowed args)
    showTerm e (con c args) = showOp agdaCon (unqualifiedName c) (showArg e <$> filter isAllowed args)
    showTerm e (def f args) = showOp agdaDef (unqualifiedName f) (showArg e <$> filter isAllowed args)
    showTerm e t            = "_"

    showType : (e : List String) → Type → String
    showType e (el _ t) = showTerm e t

  asRule′ : Type → List String → List⁺ String
  asRule′ (el _ (pi (arg i t₁) (abs "_" t₂))) acc = showType acc t₁ ∷⁺ asRule′ t₂ ("_" ∷ acc)
  asRule′ (el _ (pi (arg i t₁) (abs  x  t₂))) acc = asRule′ t₂ (x ∷ acc)
  asRule′                               t     acc = showType acc t ∷ []

  initLast′ : List⁺ String → (List String × String)
  initLast′ xs with snocView xs
  initLast′ ._ | ts ∷ʳ′ t = (ts , t)


asRule : Name → String
asRule n = forProofSty (initLast′ (asRule′ (type n) []))
  where
  forProofSty : List String × String → String
  forProofSty (ps , c) = "\\infer[" ++ n′ ++ "]{" ++ c ++ "}{" ++ ps′ ++ "}"
    where
      n′  = unqualifiedName n
      ps′ = foldr _++_ "" (intersperse " & " ps)
