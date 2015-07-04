------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Level                      using (zero)
open import Category.Monad             using (module RawMonad)
open import Coinduction                using (♭; ♯_)
open import Data.Bool                  using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Colist                using (fromList)
open import Data.List                  using (List; _∷_; []; map; foldr; any; null)
open import Data.String                using (String; _++_; unlines; toList)
open import Data.Maybe                 using (Maybe; just; nothing)
open import Function                   using (_$_; _∘_)
open import IO                         using (IO; writeFile; mapM′; _>>_)
open import Logic.ToLaTeX              using (module ToLaTeX; ToLaTeX)
open import Reflection
open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality



module Example.System.Base where


-- * setup entities
data Entity : Set where
  john  : Entity
  mary  : Entity
  bill  : Entity

abstract
  forAll : (Entity → Bool) → Bool
  forAll p = foldr (λ x b → b ∧ p x) true (john ∷ mary ∷ bill ∷ [])

  exists : (Entity → Bool) → Bool
  exists p = foldr (λ x b → b ∨ p x) false (john ∷ mary ∷ bill ∷ [])


-- * setup helper function
infixr 4 _⊃_

_⊃_ : Bool → Bool → Bool
true  ⊃ true  = true
true  ⊃ false = false
false ⊃ _     = true


-- * setup atomic formulas
data Atom : Set where
  N   : Atom
  NP  : Atom
  S   : Atom
  INF : Atom

_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)
N   ≟-Atom N   = yes refl
N   ≟-Atom NP  = no (λ ())
N   ≟-Atom S   = no (λ ())
N   ≟-Atom INF = no (λ ())
NP  ≟-Atom N   = no (λ ())
NP  ≟-Atom NP  = yes refl
NP  ≟-Atom S   = no (λ ())
NP  ≟-Atom INF = no (λ ())
S   ≟-Atom N   = no (λ ())
S   ≟-Atom NP  = no (λ ())
S   ≟-Atom S   = yes refl
S   ≟-Atom INF = no (λ ())
INF ≟-Atom N   = no (λ ())
INF ≟-Atom NP  = no (λ ())
INF ≟-Atom S   = no (λ ())
INF ≟-Atom INF = yes refl

⟦_⟧ᵁ : Atom → Set
⟦ N   ⟧ᵁ = Entity → Bool
⟦ NP  ⟧ᵁ = Entity
⟦ S   ⟧ᵁ = Bool
⟦ INF ⟧ᵁ = Entity → Bool

AtomToLaTeX : ToLaTeX Atom
AtomToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX }
  where
    toLaTeX : Atom → String
    toLaTeX N   = "n"
    toLaTeX NP  = "np"
    toLaTeX S   = "s"
    toLaTeX INF = "inf"


-- * setup abstract lexicon
postulate
  DUTCH   : Entity → Bool
  ENGLISH : Entity → Bool
  SMILES  : Entity → Bool
  LEAVES  : Entity → Bool
  CHEATS  : Entity → Bool
  TEASES  : Entity → Entity → Bool
  LOVES   : Entity → Entity → Bool
  UNICORN : Entity → Bool
  PERSON  : Entity → Bool
  TEACHER : Entity → Bool
  SAID    : Entity → Bool → Bool
  WANTS   : Entity → Bool → Bool


-- * testing semantics

open RawMonad (Data.Maybe.monad {zero}) using (_<$>_)

infix 1 Assert_

data   TestFailure : Set where
record TestSuccess : Set where

Assert_ : Bool → Set
Assert true  = TestSuccess
Assert false = TestFailure

list : Term → Maybe (List Term)
list (con (quote List._∷_) (_ ∷ _ ∷ arg _ y ∷ arg _ ys ∷ _)) = y ∷_ <$> list ys
list (con (quote List.[])   _                              ) = just []
list _                                                       = nothing


_∈_ : Term → List Term → Bool
y ∈ xs = any (λ x → ⌊ forgetAbs x ≟ forgetAbs y ⌋) xs
  where
    mutual
      forgetAbs : Term → Term
      forgetAbs (var x args)      = var x (forgetAbsArgs args)
      forgetAbs (con c args)      = con c (forgetAbsArgs args)
      forgetAbs (def f args)      = def f (forgetAbsArgs args)
      forgetAbs (lam v (abs _ x)) = lam v (abs "_" (forgetAbs x))
      forgetAbs (pi (arg i (el s₁ t₁)) (abs _ (el s₂ t₂)))
        = pi (arg i (el s₁ (forgetAbs t₁))) (abs "_" (el s₂ (forgetAbs t₂)))
      forgetAbs t = t

      forgetAbsArgs : List (Arg Term) → List (Arg Term)
      forgetAbsArgs []               = []
      forgetAbsArgs (arg i x ∷ args) = arg i (forgetAbs x) ∷ forgetAbsArgs args


_⊆_ : List Term → List Term → Bool
(y ∷ ys) ⊆ xs = (y ∈ xs) ∧ (ys ⊆ xs)
[]       ⊆ xs = true

_sameAs_ : Term → List Term → Bool
ys sameAs xs with list ys
_  sameAs xs | just ys = (ys ⊆ xs) ∧ (xs ⊆ ys)
_  sameAs xs | nothing = false


-- * writing LaTeX proofs

data Proof : Set where
  proof : (file sentence tree term : String) → Proof

mutual
  writeLaTeX : List Proof → IO _
  writeLaTeX ps = ♯ mapM′ writeProof (fromList ps) >> ♯ writeMainFile ps

  writeProof : Proof → IO _
  writeProof (proof file sentence tree term)
    = writeFile (file ++ ".tex") ∘ unlines
    $ "\\begin{figure}[ht]%"
    ∷ "\\centering%"
    ∷ tree
    ∷ mathMode term
    ∷ ("\\label{" ++ file ++ "}")
    ∷ ("\\caption{``" ++ sentence ++ "''}")
    ∷ "\\end{figure}"
    ∷ []
    where
      mathMode : String → String
      mathMode str = if null (toList str) then "" else ("$" ++ str ++ "$")

  writeMainFile : List Proof → IO _
  writeMainFile ps = writeFile "proof.tex" mainFile
    where
      includeAll : String
      includeAll = unlines (map (λ {(proof fn _ _ _) → "\\include{" ++ fn ++ "}%"}) ps)
      mainFile : String
      mainFile = unlines
        $ "\\documentclass{article}"
        ∷ preamble
        ∷ "\\begin{document}"
        ∷ includeAll
        ∷ "\\end{document}"
        ∷ []

  preamble : String
  preamble = unlines
    $ "\\usepackage{adjustbox}%"
    ∷ "\\usepackage[labelformat=empty]{caption}%"
    ∷ "\\usepackage{amssymb}%"
    ∷ "\\usepackage{amsmath}%"
    ∷ "\\usepackage{bussproofs}%"
    ∷ "\\usepackage[usenames,dvipsnames]{color}%"
    ∷ "\\usepackage{etoolbox}%"
    ∷ "\\usepackage{mdframed}%"
    ∷ "\\usepackage{pict2e}%"
    ∷ "\\usepackage{picture}%"
    ∷ "\\usepackage{scalerel}%"
    ∷ "\\usepackage{stmaryrd}%"
    ∷ "\\usepackage{textgreek}%"
    ∷ "\\usepackage{ucs}%"
    ∷ "\\usepackage[utf8x]{inputenc}%"
    ∷ "\\usepackage{xifthen}%"
    ∷ ""
    ∷ "\\EnableBpAbbreviations%"
    ∷ ""
    ∷ "\\makeatletter"
    ∷ "\\newcommand{\\pictslash}[2]{%"
    ∷ "  \\vcenter{%"
    ∷ "    \\sbox0{$\\m@th#1\\varobslash$}\\dimen0=.55\\wd0"
    ∷ "    \\hbox to\\wd 0{%"
    ∷ "      \\hfil\\pictslash@aux#2\\hfil"
    ∷ "    }%"
    ∷ "  }%"
    ∷ "}"
    ∷ "\\newcommand{\\pictslash@aux}[2]{%"
    ∷ "    \\begin{picture}(\\dimen0,\\dimen0)"
    ∷ "    \\roundcap"
    ∷ "    \\linethickness{.15ex}"
    ∷ "    \\put(0,#1\\dimen0){\\line(1,#2){\\dimen0}}"
    ∷ "    \\end{picture}%"
    ∷ "}"
    ∷ "\\makeatother"
    ∷ ""
    ∷ "\\newcommand{\\varslash}{%"
    ∷ "  \\mathbin{\\mathpalette\\pictslash{{0}{1}}}%"
    ∷ "}"
    ∷ "\\newcommand{\\varbslash}{%"
    ∷ "  \\mathbin{\\mathpalette\\pictslash{{1}{ -1}}}%"
    ∷ "}"
    ∷ "\\newcommand{\\focus}[1]{%"
    ∷ "  \\adjustbox{padding=.4em .15ex .1em .15ex,bgcolor=Cyan}{%"
    ∷ "    \\ensuremath{\\color{white}\\rule[-4pt]{0pt}{14pt}#1}"
    ∷ "  }%"
    ∷ "}"
    ∷ ""
    ∷ "\\newcommand{\\varbox}[1][]{\\ifthenelse{\\isempty{#1}}{\\Box}{\\,[\\,#1\\,]\\,}}"
    ∷ "\\newcommand{\\vardia}[1][]{\\ifthenelse{\\isempty{#1}}{\\Diamond}{\\,\\langle\\,#1\\,\\rangle\\,}}"
    ∷ "\\newcommand{\\varpref}[1]{{}_{#1}}"
    ∷ "\\newcommand{\\varsuff}[1]{{}^{#1}}"
    ∷ "\\newcommand{\\vardown}[1]{\\,\\cdot\\,#1\\,\\cdot\\,}"
    ∷ "\\renewcommand{\\fCenter}{\\mathbin{\\vdash}}"
    ∷ []
