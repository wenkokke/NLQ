module AB where

open import Level                                 using (_⊔_; zero)
open import Function                              using (_∘_; _$_)
open import Data.List                             using (List)
open import Data.List.NonEmpty                    using (List⁺)
open import Data.Product                          using (_×_)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


-- Encoding of context-free grammars in Greibach Normal Form (GNF).
module CFG {ℓ₁ ℓ₂} (Σ : Set ℓ₁) (V : Set ℓ₂) where

  -- This is a weird encoding of GNF grammars, but it ensures that the
  -- grammar must have at least one production for each word in the
  -- lexcion, even if the productions are not reachable from the start
  -- symbol.
  -- This is a crucial property if we want to be able to convert the
  -- GNF grammars to AB grammars; if we want to be able to convert
  -- arbitrary GNF grammars, we must add a unit to the grammar.
  GNF : Set (ℓ₁ ⊔ ℓ₂)
  GNF = Σ → (List⁺ (V × List V))


-- Encoding of AB grammars as deductive system, faithful to @moot2012.
module AB₀ {u} (Univ : Set u) where


  infix  1  AB_
  infix  3  _⊢_
  infixl 4  _[_]
  infixr 20 _⇒_
  infixl 20 _⇐_
  infixr 30 _⊗_ _<⊗_ _⊗>_


  data Type : Set u where
    el   : Univ → Type
    _⇒_  : Type → Type → Type
    _⇐_  : Type → Type → Type
    _⊗_  : Type → Type → Type


  data Context : Set u where
    []   : Context
    _⊗>_ : Type → Context → Context
    _<⊗_ : Context → Type → Context


  _[_] : Context → Type → Type
  []     [ B ] = B
  A ⊗> Γ [ B ] = A ⊗ (Γ [ B ])
  Γ <⊗ A [ B ] = (Γ [ B ]) ⊗ A


  data Judgement : Set u where
    _⊢_ : Type → Type → Judgement


  data AB_ : Judgement → Set u where
    ax : ∀ {A}           → AB A ⊢ A
    ⇒ₑ : ∀ {A B C}    Γ  → AB Γ [ B ] ⊢ C            → AB Γ [ A ⊗ (A ⇒ B) ] ⊢ C
    ⇐ₑ : ∀ {A B C}    Γ  → AB Γ [ B ] ⊢ C            → AB Γ [ (B ⇐ A) ⊗ A ] ⊢ C
    aᴸ : ∀ {A B C D}  Γ  → AB Γ [ (A ⊗ B) ⊗ C ] ⊢ D  → AB Γ [ A ⊗ (B ⊗ C) ] ⊢ D
    aᴿ : ∀ {A B C D}  Γ  → AB Γ [ A ⊗ (B ⊗ C) ] ⊢ D  → AB Γ [ (A ⊗ B) ⊗ C ] ⊢ D


  cut′ : ∀ {A B C} → AB A ⊢ B → AB B ⊢ C → AB A ⊢ C
  cut′    ax        g = g
  cut′ (  ⇒ₑ  Γ f)  g = ⇒ₑ  Γ (cut′ f g)
  cut′ (  ⇐ₑ  Γ f)  g = ⇐ₑ  Γ (cut′ f g)
  cut′ (  aᴸ  Γ f)  g = aᴸ  Γ (cut′ f g)
  cut′ (  aᴿ  Γ f)  g = aᴿ  Γ (cut′ f g)


  -- Operator ✓, which means "is accepted by the language defined by Lex".
  module ✓-Lex {w} (S : Univ) (Word : Set w) (Lex : Word → List⁺ Type) where

    open import Data.List          using (_∷_; []; concatMap)
    open import Data.List.NonEmpty using (_∷_; _∷⁺_; foldr₁; toList; concat; map)
    open import Data.Sum           using (_⊎_)


    flip : List⁺ (List⁺ Type) → List⁺ (List⁺ Type)
    flip (xs ∷ xss) = concat (map (λ ys → map (λ y → y ∷ ys) xs) (flip′ xss))
      where
        flip′ : List (List⁺ Type) → List⁺ (List Type)
        flip′ []         = [] ∷ []
        flip′ (xs ∷ xss) = concat (map (λ ys → map (λ y → y ∷ ys) xs) (flip′ xss))

    {-# TERMINATING #-}
    smash : List⁺ Type → Type
    smash (x     ∷ []) = x
    smash (x ∷ y ∷ xs) = x ⊗ smash (y ∷ xs)

    ✓_ : List⁺ Word → Set u
    ✓ xs = foldr₁ _⊎_ (map ((λ x → AB x ⊢ el S) ∘ smash) (flip (map Lex xs)))


  -- Operator ✓, which means "is accepted by the language defined by GNF".
  module ✓-CFG {w} (S : Univ) (Word : Set w) (_≟_ : (x y : Word) → Dec (x ≡ y)) (gnf : CFG.GNF Word Univ) where

    open import Data.Bool                  using (Bool)
    open import Data.Product               using (_,_)
    open import Data.List                  using (_∷_; []; foldl; reverse)
    open import Data.List.NonEmpty         using (map)
    open import Relation.Nullary.Decidable using (⌊_⌋)

    private
      Lex : Word → List⁺ Type
      Lex w = map toTy (gnf w)
        where
          toTy : (Univ × List Univ) → Type
          toTy (x , xs) = foldl (λ y z → y ⇐ el z) (el x) (reverse xs)

    ✓_ : List⁺ Word → Set u
    ✓ xs = ✓-Lex.✓_ S Word Lex xs


-- Encoding of AB grammars as deductive system, faithful to @moot2012.
module AB₁ {u} (Univ : Set u) where


  infix  1  AB_
  infix  3  _⊢_
  infixl 4  _[_]
  infixl 10 _&_
  infixr 20 _⇒_
  infixl 20 _⇐_
  infixr 30 _⊗_ _<⊗_ _⊗>_


  data Type : Set u where
    el   : Univ → Type
    _⇒_  : Type → Type → Type
    _⇐_  : Type → Type → Type
    _⊗_  : Type → Type → Type
    _&_  : Type → Type → Type


  data Context : Set u where
    []   : Context
    _⊗>_ : Type → Context → Context
    _<⊗_ : Context → Type → Context


  _[_] : Context → Type → Type
  []     [ B ] = B
  A ⊗> Γ [ B ] = A ⊗ (Γ [ B ])
  Γ <⊗ A [ B ] = (Γ [ B ]) ⊗ A


  data Judgement : Set u where
    _⊢_ : Type → Type → Judgement


  data AB_ : Judgement → Set u where
    ax : ∀ {A}           → AB A ⊢ A
    ⇒ₑ : ∀ {A B C}    Γ  → AB Γ [ B ] ⊢ C            → AB Γ [ A ⊗ (A ⇒ B) ] ⊢ C
    ⇐ₑ : ∀ {A B C}    Γ  → AB Γ [ B ] ⊢ C            → AB Γ [ (B ⇐ A) ⊗ A ] ⊢ C
    s₁ : ∀ {A B C}    Γ  → AB Γ [ A ] ⊢ C            → AB Γ [ A & B ] ⊢ C
    s₂ : ∀ {A B C}    Γ  → AB Γ [ B ] ⊢ C            → AB Γ [ A & B ] ⊢ C
    aᴸ : ∀ {A B C D}  Γ  → AB Γ [ (A ⊗ B) ⊗ C ] ⊢ D  → AB Γ [ A ⊗ (B ⊗ C) ] ⊢ D
    aᴿ : ∀ {A B C D}  Γ  → AB Γ [ A ⊗ (B ⊗ C) ] ⊢ D  → AB Γ [ (A ⊗ B) ⊗ C ] ⊢ D


  cut′ : ∀ {A B C} → AB A ⊢ B → AB B ⊢ C → AB A ⊢ C
  cut′    ax        g = g
  cut′ (  ⇒ₑ  Γ f)  g = ⇒ₑ  Γ (cut′ f g)
  cut′ (  ⇐ₑ  Γ f)  g = ⇐ₑ  Γ (cut′ f g)
  cut′ (  s₁  Γ f)  g = s₁  Γ (cut′ f g)
  cut′ (  s₂  Γ f)  g = s₂  Γ (cut′ f g)
  cut′ (  aᴸ  Γ f)  g = aᴸ  Γ (cut′ f g)
  cut′ (  aᴿ  Γ f)  g = aᴿ  Γ (cut′ f g)


  -- Operator ✓, which means "is accepted by the language defined by Lex".
  module ✓-Lex {w} (S : Univ) (Word : Set w) (Lex : Word → Type) where

    open import Data.List          using (_∷_; [])
    open import Data.List.NonEmpty using (_∷_; map)

    private
      {-# TERMINATING #-}
      smash : List⁺ Type → Type
      smash (x     ∷ []) = x
      smash (x ∷ y ∷ xs) = x ⊗ smash (y ∷ xs)

    ✓_ : List⁺ Word → Set u
    ✓ xs = AB smash (map Lex xs) ⊢ el S


  -- Operator ✓, which means "is accepted by the language defined by
  -- GNF".
  module ✓-CFG {w} (S : Univ) (Word : Set w) (_≟_ : (x y : Word) → Dec (x ≡ y)) (gnf : CFG.GNF Word Univ) where

    open import Data.Bool                  using (Bool)
    open import Data.Product               using (_,_)
    open import Data.List                  using (_∷_; []; foldl; reverse)
    open import Data.List.NonEmpty         using (_∷_; map)
    open import Relation.Nullary.Decidable using (⌊_⌋)

    private
      {-# TERMINATING #-}
      smash : List⁺ Type → Type
      smash (x     ∷ []) = x
      smash (x ∷ y ∷ xs) = x & smash (y ∷ xs)

      Lex : Word → Type
      Lex w = smash (map toTy (gnf w))
        where
          toTy : (Univ × List Univ) → Type
          toTy (x , xs) = foldl (λ y z → y ⇐ el z) (el x) (reverse xs)

    ✓_ : List⁺ Word → Set u
    ✓ xs = ✓-Lex.✓_ S Word Lex xs


-- Encoding of the language aⁿbⁿ for n > 0.
module aⁿbⁿ where

  open import Data.List          using (_∷_; [])
  open import Data.List.NonEmpty using (_∷_; map)
  open import Data.Product       using (_,_)
  open import Data.Sum           using (inj₁; inj₂)

  data Univ : Set where
    S : Univ
    B : Univ

  data Word : Set where
    a : Word
    b : Word

  private
    _≟_ : (x y : Word) → Dec (x ≡ y)
    a ≟ a = yes refl
    a ≟ b = no (λ ())
    b ≟ a = no (λ ())
    b ≟ b = yes refl


  -- use AB₀ and a lexicon, see if we can parse 'ab' and 'aabb'
  module _ where
    private
      open AB₀ Univ

      Lex : Word → List⁺ Type
      Lex a = el S ⇐ el B
            ∷ el S ⇐ el B ⇐ el S
            ∷ []
      Lex b = el B
            ∷ []

      open AB₀.✓-Lex Univ S Word Lex

      ab : ✓ (a ∷ b ∷ [])
      ab = inj₁ (⇐ₑ [] ax)

      aabb : ✓ (a ∷ a ∷ b ∷ b ∷ [])
      aabb = inj₂ (inj₁ prf)
        where
          prf : AB (el S ⇐ el B ⇐ el S) ⊗ (el S ⇐ el B) ⊗ el B ⊗ el B ⊢ el S
          prf = aᴸ (_ ⊗> []) (⇐ₑ (_ ⊗> ([] <⊗ _)) (aᴸ [] (⇐ₑ ([] <⊗ _) (⇐ₑ [] ax))))


  -- use AB₀ and a translated CFG, see if we can parse 'ab' and 'aabb'
  module _ where
    private
      open AB₀ Univ
      open CFG Word Univ

      CFG : GNF
      CFG a = (S ,     B ∷ [])
            ∷ (S , S ∷ B ∷ [])
            ∷ []
      CFG b = (B ,         [])
            ∷ []

      open AB₀.✓-CFG Univ S Word _≟_ CFG

      ab : ✓ (a ∷ b ∷ [])
      ab = inj₁ (⇐ₑ [] ax)

      aabb : ✓ (a ∷ a ∷ b ∷ b ∷ [])
      aabb = inj₂ (inj₁ prf)
        where
          prf : AB (el S ⇐ el B ⇐ el S) ⊗ (el S ⇐ el B) ⊗ el B ⊗ el B ⊢ el S
          prf = aᴸ (_ ⊗> []) (⇐ₑ (_ ⊗> ([] <⊗ _)) (aᴸ [] (⇐ₑ ([] <⊗ _) (⇐ₑ [] ax))))


  -- use AB₁ and a lexicon, see if we can parse 'ab' and 'aabb'
  module _ where
    private
      open AB₁ Univ

      Lex : Word → Type
      Lex a = el S ⇐ el B
            & el S ⇐ el B ⇐ el S
      Lex b = el B

      open AB₁.✓-Lex Univ S Word Lex

      ab : ✓ (a ∷ b ∷ [])
      ab = s₁ ([] <⊗ _) (⇐ₑ [] ax)

      aabb : ✓ (a ∷ a ∷ b ∷ b ∷ [])
      aabb = s₂ ([] <⊗ _)
           $ s₁ (_ ⊗> ([] <⊗ _))
           $ aᴸ (_ ⊗> []) (⇐ₑ (_ ⊗> ([] <⊗ _)) (aᴸ [] (⇐ₑ ([] <⊗ _) (⇐ₑ [] ax))))

  -- use AB₀ and a translated CFG, see if we can parse 'ab' and 'aabb'
  module _ where
    private
      open AB₁ Univ
      open CFG Word Univ

      CFG : GNF
      CFG a = (S ,     B ∷ [])
            ∷ (S , S ∷ B ∷ [])
            ∷ []
      CFG b = (B ,         [])
            ∷ []

      open AB₁.✓-CFG Univ S Word _≟_ CFG

      ab : ✓ (a ∷ b ∷ [])
      ab = s₁ ([] <⊗ _) (⇐ₑ [] ax)

      aabb : ✓ (a ∷ a ∷ b ∷ b ∷ [])
      aabb = s₂ ([] <⊗ _)
           $ s₁ (_ ⊗> ([] <⊗ _))
           $ aᴸ (_ ⊗> []) (⇐ₑ (_ ⊗> ([] <⊗ _)) (aᴸ [] (⇐ₑ ([] <⊗ _) (⇐ₑ [] ax))))


-- use AB₀ and manually annotated structures, and see if we can
-- parse some Italian.
module _ where
  private
    data Univ : Set where S N NP : Univ
    open AB₀ Univ

    s  = el S
    n  = el N
    np = el NP
    vp = np ⇒ s

    cosa    = (s ⇐ (s ⇐ np))
    guarda  = (s ⇐ vp)
    passare = (vp ⇐ np)
    il      = (np ⇐ n)
    treno   = n

    guarda_passare_il_treno : AB guarda ⊗ passare ⊗ il ⊗ treno ⊢ s
    guarda_passare_il_treno = ⇐ₑ (_ ⊗> (_ ⊗> [])) (⇐ₑ (_ ⊗> []) (⇐ₑ [] ax))
