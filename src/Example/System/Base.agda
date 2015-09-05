------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function             using (_∘_)
open import Category.Applicative using (module RawApplicative; RawApplicative)
open import Data.List            using (List; _∷_; [])
open import Data.String          using (String)
open import Data.Traversable     using (module RawTraversable; RawTraversable)
open import Logic.Polarity       using (Polarity; +; -)
open import Logic.ToLaTeX        using (module ToLaTeX; ToLaTeX)
open import Relation.Nullary     using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
open import Reflection       using (Name)


module Example.System.Base where


open import Data.Bool public using (Bool; true; false; _∧_; _∨_)
open import Reflection.Assertion public using (_↦_)


-- * Postulates

postulate
  Entity   : Set
  FORALL   : (Entity → Bool) → Bool
  EXISTS   : (Entity → Bool) → Bool
  _⊃_      : Bool → Bool → Bool


-- * Binary structures

infixr 4 _,_

data Struct {a} (A : Set a) : Set a where
  ·_·  : A                    → Struct A
  ⟨_⟩  : Struct A             → Struct A
  _,_  : Struct A → Struct A  → Struct A


rawTraversable : ∀ {a} → RawTraversable {a} Struct
rawTraversable = record { traverse = traverse′  }
  where
    open RawApplicative {{...}}
    traverse′ : ∀ {F A B} {{AppF : RawApplicative F}} → (A → F B) → Struct A → F (Struct B)
    traverse′ f  ·   x    · = ·_· <$> f x
    traverse′ f  ⟨   x    ⟩ = ⟨_⟩ <$> traverse′ f x
    traverse′ f  (l  , r  ) = _,_ <$> traverse′ f l ⊛ traverse′ f r


-- * Atomic formulas

data Atom : Set where
  N   : Atom
  Q   : Atom
  NP  : Atom
  S   : Atom
  INF : Atom
  PP  : Atom


_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)
N   ≟-Atom N   = yes refl
N   ≟-Atom Q   = no (λ ())
N   ≟-Atom NP  = no (λ ())
N   ≟-Atom S   = no (λ ())
N   ≟-Atom INF = no (λ ())
N   ≟-Atom PP  = no (λ ())
Q   ≟-Atom N   = no (λ ())
Q   ≟-Atom Q   = yes refl
Q   ≟-Atom NP  = no (λ ())
Q   ≟-Atom S   = no (λ ())
Q   ≟-Atom INF = no (λ ())
Q   ≟-Atom PP  = no (λ ())
NP  ≟-Atom N   = no (λ ())
NP  ≟-Atom Q   = no (λ ())
NP  ≟-Atom NP  = yes refl
NP  ≟-Atom S   = no (λ ())
NP  ≟-Atom INF = no (λ ())
NP  ≟-Atom PP  = no (λ ())
S   ≟-Atom N   = no (λ ())
S   ≟-Atom Q   = no (λ ())
S   ≟-Atom NP  = no (λ ())
S   ≟-Atom S   = yes refl
S   ≟-Atom INF = no (λ ())
S   ≟-Atom PP  = no (λ ())
INF ≟-Atom N   = no (λ ())
INF ≟-Atom Q   = no (λ ())
INF ≟-Atom NP  = no (λ ())
INF ≟-Atom S   = no (λ ())
INF ≟-Atom INF = yes refl
INF ≟-Atom PP  = no (λ ())
PP  ≟-Atom N   = no (λ ())
PP  ≟-Atom Q   = no (λ ())
PP  ≟-Atom NP  = no (λ ())
PP  ≟-Atom S   = no (λ ())
PP  ≟-Atom INF = no (λ ())
PP  ≟-Atom PP  = yes refl


⟦_⟧ᴬ : Atom → Set
⟦ N   ⟧ᴬ = Entity → Bool
⟦ Q   ⟧ᴬ = Entity
⟦ NP  ⟧ᴬ = Entity
⟦ S   ⟧ᴬ = Bool
⟦ INF ⟧ᴬ = Entity → Bool
⟦ PP  ⟧ᴬ = Entity


instance
  AtomToLaTeX : ToLaTeX Atom
  AtomToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX }
    where
      toLaTeX : Atom → String
      toLaTeX N   = "n"
      toLaTeX Q   = "q"
      toLaTeX NP  = "np"
      toLaTeX S   = "s"
      toLaTeX INF = "inf"
      toLaTeX PP  = "pp"


-- * Polarised atoms

data PolarisedAtom : Set where
  _⁺ : Atom → PolarisedAtom
  _⁻ : Atom → PolarisedAtom


⁺-injective : ∀ {A B} (pr : (A ⁺) ≡ (B ⁺)) → A ≡ B
⁺-injective refl = refl

⁻-injective : ∀ {A B} (pr : (A ⁻) ≡ (B ⁻)) → A ≡ B
⁻-injective refl = refl


_≟-PolarisedAtom_ : (A B : PolarisedAtom) → Dec (A ≡ B)
(A ⁺) ≟-PolarisedAtom (B ⁺) with A ≟-Atom B
(A ⁺) ≟-PolarisedAtom (B ⁺) | yes A=B = yes (cong _⁺ A=B)
(A ⁺) ≟-PolarisedAtom (B ⁺) | no  A≠B = no (A≠B ∘ ⁺-injective)
(A ⁺) ≟-PolarisedAtom (B ⁻) = no (λ ())
(A ⁻) ≟-PolarisedAtom (B ⁺) = no (λ ())
(A ⁻) ≟-PolarisedAtom (B ⁻) with A ≟-Atom B
(A ⁻) ≟-PolarisedAtom (B ⁻) | yes A=B = yes (cong _⁻ A=B)
(A ⁻) ≟-PolarisedAtom (B ⁻) | no  A≠B = no (A≠B ∘ ⁻-injective)


⟦_⟧ᴾ : PolarisedAtom → Set
⟦ A ⁺ ⟧ᴾ = ⟦ A ⟧ᴬ
⟦ A ⁻ ⟧ᴾ = ⟦ A ⟧ᴬ


Polarityᴬ? : PolarisedAtom → Polarity
Polarityᴬ? (_ ⁺) = +
Polarityᴬ? (_ ⁻) = -

instance
  PolarisedAtomToLaTeX : ToLaTeX PolarisedAtom
  PolarisedAtomToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX }
    where
      toLaTeX : PolarisedAtom → String
      toLaTeX (A ⁺) = ToLaTeX.toLaTeX AtomToLaTeX A
      toLaTeX (A ⁻) = ToLaTeX.toLaTeX AtomToLaTeX A


-- * Utility for constructing lists of Boolean values

module ListOf (A : Set) where

  [_,_] : A → A → List A
  [ x , y ] = x ∷ y ∷ []

  [_,_,_] : A → A → A → List A
  [ x , y , z ] = x ∷ y ∷ z ∷ []

  [_,_,_,_] : A → A → A → A → List A
  [ x , y , z , w ] = x ∷ y ∷ z ∷ w ∷ []


-- * Lexicon

module Default where

  data Word : Set where
    john     : Word
    mary     : Word
    bill     : Word
    unicorn  : Word
    leave    : Word
    to       : Word
    left     : Word
    smiles   : Word
    cheats   : Word
    finds    : Word
    loves    : Word
    wants    : Word
    said     : Word
    a        : Word
    some     : Word
    every    : Word
    everyone : Word
    someone  : Word


-- * Open up "print constructor as LaTeX inference rule""

isBanned : Name → Bool
isBanned (quote Atom)          = true
isBanned (quote PolarisedAtom) = true
isBanned (quote Polarityᴬ?)    = true
isBanned _                     = false

open import Reflection.Show.InferenceRule isBanned public
