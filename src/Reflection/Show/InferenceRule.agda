------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function           using (_∘_; _$_)
open import Category.Monad     using (module RawMonad)
open import Data.Bool          using (Bool; true; false; not; if_then_else_; _∧_)
open import Data.Char          using (Char) renaming (_==_ to _C==_)
open import Data.List          using (List; _∷_; []; filter; drop; break; intersperse; foldr; all; [_])
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; _∷ʳ′_; snocView)
open import Data.Maybe         using (Maybe; just; nothing; is-nothing)
open import Data.Nat           using (ℕ; zero; suc; _⊔_)
open import Data.String        using (String; toList; fromList; _++_; unlines) renaming (_==_ to _S==_)
open import Data.Product       using (_×_; _,_)
open import Reflection
open import Logic.NLIBC ℕ using (⇨ᴸ)


module Reflection.Show.InferenceRule (bannedArg : Name → Bool) where


open RawMonad {{...}} using (_<$>_)
instance
  monadList  = Data.List.monad
  monadMaybe = Data.Maybe.monad


private
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


  module Priv (bannedName : String) where

    {-# TERMINATING #-}
    showOper :  (f : String → String) (op : String) (xs : List String) → String
    showOper f op xs = showOper′ f (toList op) xs
      where
      showOper′ : (f : String → String) (op : List Char) (xs : List String) → String
      showOper′ f        []       xs  = foldr _++_ "" (intersperse " " xs)
      showOper′ f ('_' ∷ op)      []  = fromList ('_' ∷ op)
      showOper′ f ('_' ∷ op) (x ∷ xs) = x ++ showOper′ f op xs
      showOper′ f        op       xs  with break (_C== '_') op
      showOper′ f        op       xs  | (op₁ , op₂) = f (fromList op₁) ++ (showOper′ f op₂ xs)


    lookupVar : ℕ → List String → String
    lookupVar n       []      = ""
    lookupVar zero    (x ∷ _) = x
    lookupVar (suc n) (_ ∷ e) = lookupVar n e


    agdaVar agdaCon agdaDef : String → String
    agdaVar r = "\\AgdaBound{" ++ r ++ "}\\;"
    agdaCon r = if r S== bannedName then "" else "\\AgdaInductiveConstructor{" ++ r ++ "}\\;"
    agdaDef r = if r S== bannedName then "" else "\\AgdaFunction{" ++ r ++ "}\\;"


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


      showArg : (e : List String) (t : Arg Term) → String
      showArg e (arg _ t) = showTerm e t


      showTerm : (e : List String) (t : Term) → String
      showTerm e (var x args) =
        showOper agdaVar (lookupVar x e) (showArg e <$> filter allowed? args)
      showTerm e (con c args) =
        showOper agdaCon (unqualifiedName c) (showArg e <$> filter allowed? args)
      showTerm e (def f args) =
        showOper agdaDef (unqualifiedName f) (showArg e <$> filter allowed? args)
      showTerm e t = "_"


    showType : (e : List String) → Type → String
    showType e (el _ t) = showTerm e t


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
          where
            ps′ = unlines (intersperse "\\\\" ps)


private
  mathpar : String → String
  mathpar str = unlines ("\\begin{mathpar}" ∷ str ∷ "\\end{mathpar}" ∷ [])

  asString : Name → String
  asString n = fromList (filter (λ x → not (x C== '_')) (toList (unqualifiedName n)))

  joinWith : String → List String → String
  joinWith x xs = foldr _++_ "" (intersperse x xs)

  -- Layout lists of rules according to the following idea: We put line breaks
  -- between two rules if their first characters are not the same, unless this
  -- would create a sequence of rules which all are put on their own line.
  layout : (Name → String) → List Name → String
  layout f []       = ""
  layout f (n ∷ []) = f n
  layout f (n ∷ ns) =
    joinWith "\\\\\\\\" (joinWith "\\and" <$> ((f <$>_) <$> merge (groupBy _H==_ n ns)))
    where
    _H==_ : Name → Name → Bool
    _H==_ x y with toList (unqualifiedName x) | toList (unqualifiedName y)
    _H==_ _ _ |     [] |     [] = true
    _H==_ _ _ | x ∷ xs | y ∷ ys = x C== y
    _H==_ _ _ | _      | _      = false

    _∷₁_ : ∀ {a} {A : Set a} → A → List (List A) → List (List A)
    x ∷₁ [] = [ [ x ] ]
    x ∷₁ (xs ∷ xss) = (x ∷ xs) ∷ xss

    groupBy : ∀ {a} {A : Set a} (eq : A → A → Bool) → A → List A → List (List A)
    groupBy eq x []       = [ [ x ] ]
    groupBy eq x (y ∷ []) = if eq x y then [ x ∷ y ∷ [] ] else [ x ] ∷ [ y ] ∷ []
    groupBy eq x (y ∷ ys) = if eq x y then x ∷₁ (groupBy eq y ys) else [ x ] ∷ groupBy eq y ys

    merge : ∀ {a} {A : Set a} → List (List A) → List (List A)
    merge []                          = []
    merge ((x ∷ []) ∷ (y ∷ []) ∷ xss) = x ∷₁ merge ((y ∷ []) ∷ xss)
    merge (xs ∷ xss)                  = xs ∷ merge xss


_asInferRuleOf_ : Name → Name → String
n asInferRuleOf n′ = mathpar (Priv.asInferRule (asString n′) n)

_asMathParOf_ : List Name → Name → String
ns asMathParOf n = mathpar (layout (Priv.asInferRule (asString n)) ns)

asMathPar : Name → String
asMathPar n with definition n
asMathPar n | function   _ = "error: " ++ showName n ++ " is a function."
asMathPar n | record′    _ = "error: " ++ showName n ++ " is a record."
asMathPar n | axiom        = "error: " ++ showName n ++ " is an axiom."
asMathPar n | primitive′   = "error: " ++ showName n ++ " is a primitive."
asMathPar n | constructor′ = mathpar (Priv.asInferRule (asString n) n)
asMathPar n | data-type  x = constructors x asMathParOf n
