------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Level                      using (zero)
open import Category.Monad             using (module RawMonad)
open import Category.Applicative       using (module RawApplicative; RawApplicative)
open import Coinduction                using (♭; ♯_)
open import Data.Bool                  using (Bool; true; false; _∨_; if_then_else_)
open import Data.Char                  using (Char)
open import Data.Colist as C           using (fromList)
open import Data.List   as L           using (List; _∷_; []; map; foldr; any; null)
open import Data.String as S           using (String; _++_; unlines; toList; fromList)
open import Data.Maybe                 using (Maybe; just; nothing; From-just; from-just)
open import Data.Nat                   using (ℕ; suc; zero)
open import Data.Traversable           using (RawTraversable)
open import Data.Vec    as V           using (Vec; _∷_; [])
open import Function                   using (_$_; _∘_)
open import IO                         using (IO; writeFile; mapM′; _>>_)
open import Logic.ToLaTeX              using (module ToLaTeX; ToLaTeX)
open import Reflection
open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality



module Example.System.Base where


open import Data.Bool public using (_∧_)



-- * Set up a set of words

data Word : Set where

  john       : Word
  mary       : Word
  bill       : Word
  unicorn    : Word
  leave      : Word
  to         : Word
  left       : Word
  smiles     : Word
  cheats     : Word
  finds      : Word
  loves      : Word
  wants      : Word
  said       : Word
  a          : Word
  some       : Word
  every      : Word
  everyone   : Word
  someone    : Word



-- * Set up a set of meaning postulates

infix  9 _TEASES_ _LOVES_ _FINDS_ _SAID_ _WANTS_

postulate
  Entity   : Set
  FORALL   : (Entity → Bool) → Bool
  EXISTS   : (Entity → Bool) → Bool
  JOHN     : Entity
  MARY     : Entity
  BILL     : Entity
  DUTCH    : Entity → Bool
  ENGLISH  : Entity → Bool
  SMILES   : Entity → Bool
  LEAVES   : Entity → Bool
  CHEATS   : Entity → Bool
  _TEASES_ : Entity → Entity → Bool
  _LOVES_  : Entity → Entity → Bool
  _FINDS_  : Entity → Entity → Bool
  UNICORN  : Entity → Bool
  PERSON   : Entity → Bool
  _SAID_   : Entity → Bool → Bool
  _WANTS_  : Entity → Bool → Bool


-- * Implement implication.

infixr 6 _⊃_

_⊃_ : Bool → Bool → Bool
true  ⊃ false = false
_     ⊃ _     = true


-- * Implement binary trees as structures (with ⟨_⟩ denoting scope islands)

infixr 4 _,_

data Struct {a} (A : Set a) : Set a where
  ·_·  : A                    → Struct A
  ⟨_⟩  : Struct A             → Struct A
  _,_  : Struct A → Struct A  → Struct A


rawTraversable : ∀ {a} → RawTraversable {a} Struct
rawTraversable = record { traverse = traverse  }
  where
  open RawApplicative {{...}}
  traverse : ∀ {F A B} {{AppF : RawApplicative F}} → (A → F B) → Struct A → F (Struct B)
  traverse f  ·   x    · = ·_· <$> f x
  traverse f  ⟨   x    ⟩ = ⟨_⟩ <$> traverse f x
  traverse f  (l  , r  ) = _,_ <$> traverse f l ⊛ traverse f r


-- * Set up atomic formulas
data Atom : Set where
  N   : Atom
  NP  : Atom
  S   : Atom
  INF : Atom
  PP  : Atom

_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)
N   ≟-Atom N   = yes refl
N   ≟-Atom NP  = no (λ ())
N   ≟-Atom S   = no (λ ())
N   ≟-Atom INF = no (λ ())
N   ≟-Atom PP  = no (λ ())
NP  ≟-Atom N   = no (λ ())
NP  ≟-Atom NP  = yes refl
NP  ≟-Atom S   = no (λ ())
NP  ≟-Atom INF = no (λ ())
NP  ≟-Atom PP  = no (λ ())
S   ≟-Atom N   = no (λ ())
S   ≟-Atom NP  = no (λ ())
S   ≟-Atom S   = yes refl
S   ≟-Atom INF = no (λ ())
S   ≟-Atom PP  = no (λ ())
INF ≟-Atom N   = no (λ ())
INF ≟-Atom NP  = no (λ ())
INF ≟-Atom S   = no (λ ())
INF ≟-Atom INF = yes refl
INF ≟-Atom PP  = no (λ ())
PP  ≟-Atom N   = no (λ ())
PP  ≟-Atom NP  = no (λ ())
PP  ≟-Atom S   = no (λ ())
PP  ≟-Atom INF = no (λ ())
PP  ≟-Atom PP  = yes refl

⟦_⟧ᵁ : Atom → Set
⟦ N   ⟧ᵁ = Entity → Bool
⟦ NP  ⟧ᵁ = Entity
⟦ S   ⟧ᵁ = Bool
⟦ INF ⟧ᵁ = Entity → Bool
⟦ PP  ⟧ᵁ = Entity

AtomToLaTeX : ToLaTeX Atom
AtomToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX }
  where
    toLaTeX : Atom → String
    toLaTeX N   = "n"
    toLaTeX NP  = "np"
    toLaTeX S   = "s"
    toLaTeX INF = "inf"
    toLaTeX PP  = "pp"

-- * testing semantics

open RawMonad (Data.Maybe.monad {Level.zero}) using (_<$>_)

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


_words_ : (k : ℕ) → String → Maybe (Vec String k)
k words str = toVec (map S.fromList (split (toList str)))
  where
    toVec : ∀ {k} {A : Set} → List A → Maybe (Vec A k)
    toVec {zero}       []  = just []
    toVec {zero}       xs  = nothing
    toVec {suc k}      []  = nothing
    toVec {suc k} (x ∷ xs) = (x ∷_) <$> toVec xs

    split : List Char → List (List Char)
    split        []  = []
    split (' ' ∷ xs) = [] ∷ split xs
    split ( x  ∷ xs) with split xs
    split ( x  ∷ xs) |     [] = (x ∷ []) ∷ []
    split ( x  ∷ xs) | w ∷ ws = (x ∷ w ) ∷ ws


mutual
  writeLaTeX : List Proof → IO _
  writeLaTeX ps = ♯ mapM′ writeProof (C.fromList ps) >> ♯ writeMainFile ps

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
    ∷ "\\usepackage{ucs}%"
    ∷ "\\usepackage[utf8x]{inputenc}%"
    ∷ "\\DeclareUnicodeCharacter{8743}{\\ensuremath{\\wedge}}%"
    ∷ "\\DeclareUnicodeCharacter{8835}{\\ensuremath{\\supset}}%"
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
