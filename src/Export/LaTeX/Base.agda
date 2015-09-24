------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function           using (_∘_; _$_)
open import Category.Monad     using (module RawMonad)
open import Data.Bool          using (Bool; true; false; not; if_then_else_; _∧_)
open import Data.Char          using (Char) renaming (_==_ to _C==_)
open import Data.List          using (List; _∷_; []; filter; drop; break; map; intersperse; foldr; all; [_])
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; _∷ʳ′_; snocView)
open import Data.Maybe         using (Maybe; just; nothing; is-nothing)
open import Data.Nat           using (ℕ; zero; suc; _⊔_)
open import Data.String        using (String; toList; fromList; _++_; unlines) renaming (_==_ to _S==_)
open import Data.Product       using (_×_; _,_)
open import Reflection


module Export.LaTeX.Base (bannedArg : Name → Bool) where


open RawMonad {{...}} using (_<$>_)


instance
  monadList  = Data.List.monad
  monadMaybe = Data.Maybe.monad


unqualifiedName : Name → String
unqualifiedName n = if bannedArg n then "" else
  fromList (unqualifiedName′ (toList (showName n)))
  where
    lastIndex : ℕ → Char → List Char → ℕ
    lastIndex i x      []  = 0
    lastIndex i x (y ∷ ys) = if x C== y then i ⊔ j else j
      where
        j = lastIndex (suc i) x ys
    unqualifiedName′ : List Char → List Char
    unqualifiedName′ n = drop (suc (lastIndex 0 '.' n)) n


escape : List Char → List Char
escape []         = []
escape ('_' ∷ xs) = '\\' ∷ '_' ∷ escape xs
escape ('&' ∷ xs) = '\\' ∷ '&' ∷ escape xs
escape ( x  ∷ xs) =         x  ∷ escape xs

concat : List String → String
concat = foldr _++_ "" ∘ intersperse " "

parens : String → String
parens x = "(" ++ x ++ ")"


module Show (bannedName : String) where

  oper  : (namePart : String → String) (op : String) (xs : List String) → String
  oper showNP op xs = oper′ showNP (toList op) xs
    where
    oper′ : (namePart : String → String) (op : List Char) (xs : List String) → String
    oper′ showNP []      xs  = concat xs
    oper′ showNP op      []  = showNP (fromList (escape op))
    oper′ showNP op (x ∷ xs) with break (_C== '_') op
    oper′ showNP op (x ∷ xs) | (_   ,     []) = concat (showNP (fromList (escape op)) ∷ (x ∷ xs))
    oper′ showNP _  (x ∷ xs) | (op  , _ ∷ []) = concat (showNP (fromList (escape op)) ∷ (x ∷ xs))
    oper′ showNP _  (x ∷ xs) | (op₁ , _ ∷ op) = showNP (fromList (escape op₁)) ++ x ++ oper′ showNP op xs


  agdaVar agdaCon agdaDef : String → String
  agdaVar r = "\\AgdaBound{" ++ r ++ "}\\;"
  agdaCon r = if r S== bannedName then "" else "\\AgdaInductiveConstructor{" ++ r ++ "}\\;"
  agdaDef r = if r S== bannedName then "" else "\\AgdaFunction{" ++ r ++ "}\\;"


  lookupVar : ℕ → List String → String
  lookupVar n       []      = ""
  lookupVar zero    (x ∷ _) = x
  lookupVar (suc n) (_ ∷ e) = lookupVar n e


  {-# TERMINATING #-}
  mutual
    allowed? : Arg Term → Bool
    allowed? (arg i t) = visible? i ∧ not (banned? t)
      where
      banned? : Term → Bool
      banned? (con c _) = bannedArg c
      banned? (def f _) = bannedArg f
      banned?        _  = false
      visible? : Arg-info → Bool
      visible? (arg-info visible _) = true
      visible? (arg-info _       _) = false


    sarg : (e : List String) (t : Arg Term) → String
    sarg e (arg _ t) = term e t


    term : (e : List String) (t : Term) → String
    term e (var x args) = oper agdaVar (lookupVar x e) (sarg e <$> filter allowed? args)
    term e (con c args) = oper agdaCon (unqualifiedName c) (sarg e <$> filter allowed? args)
    term e (def f args) = oper agdaDef (unqualifiedName f) (sarg e <$> filter allowed? args)
    term e t = ""


  showType : (e : List String) → Type → String
  showType e (el _ t) = term e t


  splitType : Type → List String → List⁺ String
  splitType (el _ (pi (arg i t₁) (abs "_" t₂))) acc = showType acc t₁ ∷⁺ splitType t₂ ("_" ∷ acc)
  splitType (el _ (pi (arg i t₁) (abs  x  t₂))) acc = splitType t₂ (x ∷ acc)
  splitType                               t     acc = showType acc t ∷ []


  premsAndConc : List⁺ String → (List String × String)
  premsAndConc xs with snocView xs
  premsAndConc ._ | ts ∷ʳ′ t = (ts , t)

  asInferRule : Name → String
  asInferRule n = go (premsAndConc (splitType (type n) []))
    where
    n′ = unqualifiedName n
    go : List String × String → String
    go ([] , c) = "\\inferrule*[left=" ++ n′ ++ "]{ }{" ++ c ++ "}"
    go (ps , c) = "\\inferrule*[left=" ++ n′ ++ "]{" ++ ps′ ++ "}{" ++ c ++ "}"
      where ps′ = unlines (intersperse "\\\\" ps)

mathpar : String → String
mathpar str = unlines ("\\begin{mathpar}" ∷ str ∷ "\\end{mathpar}" ∷ [])

asString : Name → String
asString n = fromList (filter (λ x → not (x C== '_')) (toList (unqualifiedName n)))

joinWith : String → List String → String
joinWith x xs = foldr _++_ "" (intersperse x xs)
