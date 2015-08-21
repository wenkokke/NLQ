------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Bool     as Bool    using (Bool; true; false)
open import Data.Char     as Char    using (Char)
open import Data.Float    as Float   using ()
open import Data.List     as List    using (List; _∷_; []; foldr; reverse; filter)
open import Data.Maybe    as Mabybe  using (Maybe; just; nothing)
open import Data.Nat      as Nat     using (ℕ; suc; zero)
open import Data.Nat.Show as NatShow using ()
open import Data.String   as String  using (String; _++_; toList; fromList)
open import Reflection


module Reflection.Show where


private
  infixr 5 _∙_

  _∙_ : String → String → String
  f ∙ x = f ++ " " ++ x

  ⟨_⟩ : String → String
  ⟨ f ⟩ = "(" ++ f ++ ")"

  push : String → (ℕ → String) → (ℕ → String)
  push s e  zero   = s
  push s e (suc i) = e i

  isBinaryOp : String → Maybe String
  isBinaryOp n with reverse (toList n)
  isBinaryOp n | '_' ∷ rest with reverse rest
  isBinaryOp n | '_' ∷ rest | '_' ∷ op = just (fromList op)
  isBinaryOp n | '_' ∷ rest |  _       = nothing
  isBinaryOp n |  _                    = nothing

  isVisible : Arg Term → Bool
  isVisible (arg (arg-info visible r) x) = true
  isVisible (arg (arg-info _       r) x) = false


{-# TERMINATING #-}
mutual
  show : Term → String
  show = show′ (λ _ → "_")

  private
    show′ : (ℕ → String) → Term → String
    show′ e (var x args)              = showFun e (e x) args
    show′ e (con c args)              = showFun e (showBaseName c) args
    show′ e (def f args)              = showFun e (showBaseName f) args
    show′ e (lam visible   (abs s x)) = ⟨ "λ" ∙ s ∙ "→" ∙ show′ (push s e) x ⟩
    show′ e (lam hidden    (abs s x)) = show′ e x
    show′ e (lam instance′ (abs s x)) = show′ e x
    show′ e (lit (nat x))             = NatShow.show x
    show′ e (lit (float x))           = Float.show x
    show′ e (lit (char x))            = Char.show x
    show′ e (lit (string x))          = String.show x
    show′ e (lit (name x))            = showName x
    show′ e (quote-goal (abs x t))    = "quoteGoal" ∙ x ∙ "in " ∙ show′ e t
    show′ e (quote-term t)            = "quoteTerm" ∙ show′ e t
    show′ e quote-context             = "quoteContext"
    show′ e (unquote-term t args)     = "unquote" ∙ showFun e ⟨ show′ e t ⟩ args
    show′ e (pat-lam cs args)         = "undefined"
    show′ e (pi t₁ t₂)                = "undefined"
    show′ e (sort s)                  = "undefined"
    show′ e unknown                   = "undefined"

    showArg : (ℕ → String) → Arg Term → String → String
    showArg e (arg (arg-info visible   _) x) f = ⟨ f ∙ show′ e x ⟩
    showArg e (arg (arg-info hidden    _) x) f =   f
    showArg e (arg (arg-info instance′ _) x) f =   f

    showFun : (e : ℕ → String) (fun : String) (args : List (Arg Term)) → String
    showFun e f [] = f
    showFun e f args with isBinaryOp f | filter isVisible args
    ... | just op | (arg _ x ∷ arg _ y ∷ []) = show′ e x ∙ op ∙ show′ e y
    ... | _       | _                        = foldr (showArg e) f args

    showBaseName : Name → String
    showBaseName n = fromList (go (toList (showName n)) [])
      where
        go : List Char → List Char → List Char
        go        []  ys = reverse ys
        go ('.' ∷ xs) ys = go xs []
        go ( x  ∷ xs) ys = go xs (x ∷ ys)
