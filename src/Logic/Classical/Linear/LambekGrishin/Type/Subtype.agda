------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function                                   using (id; _∘_)
open import Data.Empty                                 using (⊥; ⊥-elim)
open import Data.Fin                                   using (Fin; suc; zero; inject+; raise)
open import Data.Nat                                   using (suc; zero; _+_)
open import Data.Product                               using (∃; Σ-syntax; _,_; uncurry)
open import Data.Sum                                   using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Vec                                   using (Vec; _∷_; []; _++_; lookup)
open import Data.Vec.Properties                        using (lookup-++-inject+)
open import Relation.Nullary                           using (¬_; Dec; yes; no)
open import Relation.Binary                            using (module DecSetoid; IsPartialOrder; IsDecPartialOrder; IsStrictPartialOrder; IsDecStrictPartialOrder)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl; cong; sym; inspect)


module Logic.Classical.Linear.LambekGrishin.Type.Subtype {ℓ} (Univ : Set ℓ) (_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)) where


open import Logic.Classical.Linear.LambekGrishin.Type            Univ as T
open import Logic.Classical.Linear.LambekGrishin.Type.Complexity Univ
open import Logic.Classical.Linear.LambekGrishin.Type.Context    Univ as C hiding (module Simple)

open T.DecEq _≟-Univ_ using (decSetoid)
open C.DecEq _≟-Univ_ using (decSetoid)
open C.Simple  using (_[_]; _<_>; <>-def; []-resp-≡)
open DecSetoid {{...}} using (_≟_)


_⊆_ : (A B : Type) → Set ℓ
A ⊆ B = ∃ (λ Χ → Χ [ A ] ≡ B)

import Relation.Binary.NonStrictToStrict _≡_ _⊆_ as ⊂
open ⊂ public using () renaming (_<_ to _⊂_)

_⊈_ : (A B : Type) → Set ℓ
A ⊈ B = ¬ A ⊆ B

_⊄_ : (A B : Type) → Set ℓ
A ⊄ B = ¬ A ⊂ B


-- Lemma: we can weaken the subtype relation by adding a context to
-- the right-handed side.
weaken : ∀ {A B} Ξ → A ⊆ B → A ⊆ Ξ [ B ]
weaken {A} {B} Ξ₁ (Ξ₂ , p) = (Ξ₁ < Ξ₂ > , P.trans (<>-def Ξ₁ Ξ₂ A) ([]-resp-≡ Ξ₁ p))


-- Lemma: only a primitive type can be the subtype of a primitive type.
A⊆elB→A=elB : ∀ {A B} → A ⊆ el B → A ≡ el B
A⊆elB→A=elB (Ξ , Ξ[A]=elB) with is-[]? Ξ
...| yes Ξ=[] rewrite Ξ=[] = Ξ[A]=elB
...| no  Ξ≠[] = ⊥-elim (Γ≠[]→elB≠Γ[A] Ξ Ξ≠[] (sym Ξ[A]=elB))

-- Lemma: no type can be the strict subtype of a primitive type.
A⊄elB : ∀ {A B} → A ⊄ el B
A⊄elB (A⊆elB , A≠B) = A≠B (A⊆elB→A=elB A⊆elB)


-- Lemma: the `⇒` constructor injects into the subtype relations.
⇒-inj-⊆ : ∀ {A B C} → A ⊆ B ⇒ C → A ≡ B ⇒ C ⊎ (A ⊆ B ⊎ A ⊆ C)
⇒-inj-⊆ (   []  , refl) = inj₁ refl
⇒-inj-⊆ (B ⇒> Ξ , refl) = inj₂ (inj₂ (Ξ , refl))
⇒-inj-⊆ (Ξ <⇒ C , refl) = inj₂ (inj₁ (Ξ , refl))
⇒-inj-⊆ (_ ⊗> _ , ())
⇒-inj-⊆ (_ ⇛> _ , ())
⇒-inj-⊆ (_ ⇚> _ , ())
⇒-inj-⊆ (_ ⊕> _ , ())
⇒-inj-⊆ (_ ⇐> _ , ())
⇒-inj-⊆ (_ <⊗ _ , ())
⇒-inj-⊆ (_ <⇛ _ , ())
⇒-inj-⊆ (_ <⇚ _ , ())
⇒-inj-⊆ (_ <⊕ _ , ())
⇒-inj-⊆ (_ <⇐ _ , ())

⇒-inj-⊂ : ∀ {A B C} → A ⊂ B ⇒ C → A ⊆ B ⊎ A ⊆ C
⇒-inj-⊂ (A⊆B⇒C , A≠B) = [ ⊥-elim ∘ A≠B , id ]′ (⇒-inj-⊆ A⊆B⇒C)


-- Lemma: the `⇐` constructor injects into the subtype relations.
⇐-inj-⊆ : ∀ {A B C} → A ⊆ B ⇐ C → A ≡ B ⇐ C ⊎ (A ⊆ B ⊎ A ⊆ C)
⇐-inj-⊆ (   []  , refl) = inj₁ refl
⇐-inj-⊆ (B ⇐> Ξ , refl) = inj₂ (inj₂ (Ξ , refl))
⇐-inj-⊆ (Ξ <⇐ C , refl) = inj₂ (inj₁ (Ξ , refl))
⇐-inj-⊆ (_ ⊗> _ , ())
⇐-inj-⊆ (_ ⇛> _ , ())
⇐-inj-⊆ (_ ⇚> _ , ())
⇐-inj-⊆ (_ ⊕> _ , ())
⇐-inj-⊆ (_ ⇒> _ , ())
⇐-inj-⊆ (_ <⊗ _ , ())
⇐-inj-⊆ (_ <⇛ _ , ())
⇐-inj-⊆ (_ <⇚ _ , ())
⇐-inj-⊆ (_ <⊕ _ , ())
⇐-inj-⊆ (_ <⇒ _ , ())

⇐-inj-⊂ : ∀ {A B C} → A ⊂ B ⇐ C → A ⊆ B ⊎ A ⊆ C
⇐-inj-⊂ (A⊆B⇐C , A≠B) = [ ⊥-elim ∘ A≠B , id ]′ (⇐-inj-⊆ A⊆B⇐C)

-- Lemma: the `⇛` constructor injects into the subtype relations.
⇛-inj-⊆ : ∀ {A B C} → A ⊆ B ⇛ C → A ≡ B ⇛ C ⊎ (A ⊆ B ⊎ A ⊆ C)
⇛-inj-⊆ (   []  , refl) = inj₁ refl
⇛-inj-⊆ (B ⇛> Ξ , refl) = inj₂ (inj₂ (Ξ , refl))
⇛-inj-⊆ (Ξ <⇛ C , refl) = inj₂ (inj₁ (Ξ , refl))
⇛-inj-⊆ (_ ⊗> _ , ())
⇛-inj-⊆ (_ ⇚> _ , ())
⇛-inj-⊆ (_ ⇐> _ , ())
⇛-inj-⊆ (_ ⊕> _ , ())
⇛-inj-⊆ (_ ⇒> _ , ())
⇛-inj-⊆ (_ <⊗ _ , ())
⇛-inj-⊆ (_ <⇚ _ , ())
⇛-inj-⊆ (_ <⇐ _ , ())
⇛-inj-⊆ (_ <⊕ _ , ())
⇛-inj-⊆ (_ <⇒ _ , ())

⇛-inj-⊂ : ∀ {A B C} → A ⊂ B ⇛ C → A ⊆ B ⊎ A ⊆ C
⇛-inj-⊂ (A⊆B⇛C , A≠B) = [ ⊥-elim ∘ A≠B , id ]′ (⇛-inj-⊆ A⊆B⇛C)


-- Lemma: the `⇚` constructor injects into the subtype relations.
⇚-inj-⊆ : ∀ {A B C} → A ⊆ B ⇚ C → A ≡ B ⇚ C ⊎ (A ⊆ B ⊎ A ⊆ C)
⇚-inj-⊆ (   []  , refl) = inj₁ refl
⇚-inj-⊆ (B ⇚> Ξ , refl) = inj₂ (inj₂ (Ξ , refl))
⇚-inj-⊆ (Ξ <⇚ C , refl) = inj₂ (inj₁ (Ξ , refl))
⇚-inj-⊆ (_ ⊗> _ , ())
⇚-inj-⊆ (_ ⇛> _ , ())
⇚-inj-⊆ (_ ⇐> _ , ())
⇚-inj-⊆ (_ ⊕> _ , ())
⇚-inj-⊆ (_ ⇒> _ , ())
⇚-inj-⊆ (_ <⊗ _ , ())
⇚-inj-⊆ (_ <⇛ _ , ())
⇚-inj-⊆ (_ <⇐ _ , ())
⇚-inj-⊆ (_ <⊕ _ , ())
⇚-inj-⊆ (_ <⇒ _ , ())

⇚-inj-⊂ : ∀ {A B C} → A ⊂ B ⇚ C → A ⊆ B ⊎ A ⊆ C
⇚-inj-⊂ (A⊆B⇚C , A≠B) = [ ⊥-elim ∘ A≠B , id ]′ (⇚-inj-⊆ A⊆B⇚C)


-- Lemma: the `⊗` constructor injects into the subtype relations.
⊗-inj-⊆ : ∀ {A B C} → A ⊆ B ⊗ C → A ≡ B ⊗ C ⊎ (A ⊆ B ⊎ A ⊆ C)
⊗-inj-⊆ (   []  , refl) = inj₁ refl
⊗-inj-⊆ (B ⊗> Ξ , refl) = inj₂ (inj₂ (Ξ , refl))
⊗-inj-⊆ (Ξ <⊗ C , refl) = inj₂ (inj₁ (Ξ , refl))
⊗-inj-⊆ (_ ⇚> _ , ())
⊗-inj-⊆ (_ ⇛> _ , ())
⊗-inj-⊆ (_ ⇐> _ , ())
⊗-inj-⊆ (_ ⊕> _ , ())
⊗-inj-⊆ (_ ⇒> _ , ())
⊗-inj-⊆ (_ <⇚ _ , ())
⊗-inj-⊆ (_ <⇛ _ , ())
⊗-inj-⊆ (_ <⇐ _ , ())
⊗-inj-⊆ (_ <⊕ _ , ())
⊗-inj-⊆ (_ <⇒ _ , ())

⊗-inj-⊂ : ∀ {A B C} → A ⊂ B ⊗ C → A ⊆ B ⊎ A ⊆ C
⊗-inj-⊂ (A⊆B⊗C , A≠B) = [ ⊥-elim ∘ A≠B , id ]′ (⊗-inj-⊆ A⊆B⊗C)


-- Lemma: the `⊕` constructor injects into the subtype relations.
⊕-inj-⊆ : ∀ {A B C} → A ⊆ B ⊕ C → A ≡ B ⊕ C ⊎ (A ⊆ B ⊎ A ⊆ C)
⊕-inj-⊆ (   []  , refl) = inj₁ refl
⊕-inj-⊆ (B ⊕> Ξ , refl) = inj₂ (inj₂ (Ξ , refl))
⊕-inj-⊆ (Ξ <⊕ C , refl) = inj₂ (inj₁ (Ξ , refl))
⊕-inj-⊆ (_ ⇚> _ , ())
⊕-inj-⊆ (_ ⇛> _ , ())
⊕-inj-⊆ (_ ⇐> _ , ())
⊕-inj-⊆ (_ ⊗> _ , ())
⊕-inj-⊆ (_ ⇒> _ , ())
⊕-inj-⊆ (_ <⇚ _ , ())
⊕-inj-⊆ (_ <⇛ _ , ())
⊕-inj-⊆ (_ <⇐ _ , ())
⊕-inj-⊆ (_ <⊗ _ , ())
⊕-inj-⊆ (_ <⇒ _ , ())

⊕-inj-⊂ : ∀ {A B C} → A ⊂ B ⊕ C → A ⊆ B ⊎ A ⊆ C
⊕-inj-⊂ (A⊆B⊕C , A≠B) = [ ⊥-elim ∘ A≠B , id ]′ (⊕-inj-⊆ A⊆B⊕C)


-- basic lemmas for ⊆ are kept private, as they will be exported as
-- part of the DecPartialOrder instance.
module Simple where

  reflexive : ∀ {A B} → A ≡ B → A ⊆ B
  reflexive A=B rewrite A=B = ([] , refl)

  trans : ∀ {A B C} → A ⊆ B → B ⊆ C → A ⊆ C
  trans {A} {B} {C} (Ξ₁ , p₁) (Ξ₂ , p₂) = Ξ₂ < Ξ₁ > ,
    P.trans (<>-def Ξ₂ Ξ₁ A) (P.trans ([]-resp-≡ Ξ₂ p₁) p₂)

  antisym : ∀ {A B} → A ⊆ B → B ⊆ A → A ≡ B
  antisym {A} (Ξ₁ , p₁  ) (Ξ₂ , p₂) with Ξ₁ ≟ []
  antisym {A} (Ξ₁ , p₁  ) (Ξ₂ , p₂) | yes Ξ₁=[] rewrite Ξ₁=[] = p₁
  antisym {A} (Ξ₁ , refl) (Ξ₂ , p₂) | no  Ξ₁≠[] =
    ⊥-elim (Γ≠[]→A≠Γ[A] A (Ξ₂ < Ξ₁ >) (Γ≠[]→Δ<Γ>≠[] Ξ₁ Ξ₂ Ξ₁≠[]) (sym (P.trans (<>-def Ξ₂ Ξ₁ A) p₂)))


  _⊆?_ : ∀ A B → Dec (A ⊆ B)
  A ⊆? B with (A ≟ B)
  A ⊆? B | yes A=B = yes ([] , A=B)
  A ⊆? (el B)  | no  A≠B = no (A≠B ∘ A⊆elB→A=elB)
  A ⊆? (B ⇒ C) | no  A≠B with A ⊆? B | A ⊆? C
  ...| yes A⊆B | _       = yes (weaken ([] <⇒ C) A⊆B)
  ...| _       | yes A⊆C = yes (weaken (B ⇒> []) A⊆C)
  ...| no  A⊈B | no  A⊈C = no  ([ A≠B , [ A⊈B , A⊈C ]′ ]′ ∘ ⇒-inj-⊆)
  A ⊆? (B ⇐ C) | no  A≠B with A ⊆? B | A ⊆? C
  ...| yes A⊆B | _       = yes (weaken ([] <⇐ C) A⊆B)
  ...| _       | yes A⊆C = yes (weaken (B ⇐> []) A⊆C)
  ...| no  A⊈B | no  A⊈C = no  ([ A≠B , [ A⊈B , A⊈C ]′ ]′ ∘ ⇐-inj-⊆)
  A ⊆? (B ⇚ C) | no  A≠B with A ⊆? B | A ⊆? C
  ...| yes A⊆B | _       = yes (weaken ([] <⇚ C) A⊆B)
  ...| _       | yes A⊆C = yes (weaken (B ⇚> []) A⊆C)
  ...| no  A⊈B | no  A⊈C = no  ([ A≠B , [ A⊈B , A⊈C ]′ ]′ ∘ ⇚-inj-⊆)
  A ⊆? (B ⇛ C) | no  A≠B with A ⊆? B | A ⊆? C
  ...| yes A⊆B | _       = yes (weaken ([] <⇛ C) A⊆B)
  ...| _       | yes A⊆C = yes (weaken (B ⇛> []) A⊆C)
  ...| no  A⊈B | no  A⊈C = no  ([ A≠B , [ A⊈B , A⊈C ]′ ]′ ∘ ⇛-inj-⊆)
  A ⊆? (B ⊗ C) | no  A≠B with A ⊆? B | A ⊆? C
  ...| yes A⊆B | _       = yes (weaken ([] <⊗ C) A⊆B)
  ...| _       | yes A⊆C = yes (weaken (B ⊗> []) A⊆C)
  ...| no  A⊈B | no  A⊈C = no  ([ A≠B , [ A⊈B , A⊈C ]′ ]′ ∘ ⊗-inj-⊆)
  A ⊆? (B ⊕ C) | no  A≠B with A ⊆? B | A ⊆? C
  ...| yes A⊆B | _       = yes (weaken ([] <⊕ C) A⊆B)
  ...| _       | yes A⊆C = yes (weaken (B ⊕> []) A⊆C)
  ...| no  A⊈B | no  A⊈C = no  ([ A≠B , [ A⊈B , A⊈C ]′ ]′ ∘ ⊕-inj-⊆)


isPartialOrder : IsPartialOrder _≡_ _⊆_
isPartialOrder = record
  { isPreorder = record
    { isEquivalence = P.isEquivalence
    ; reflexive     = reflexive
    ; trans         = trans
    }
  ; antisym = antisym
  }
  where open Simple


isDecPartialOrder : IsDecPartialOrder _≡_ _⊆_
isDecPartialOrder = record
  { isPartialOrder = isPartialOrder
  ; _≟_            = _≟_
  ; _≤?_           = _⊆?_
  }
  where open Simple


isStrictPartialOrder : IsStrictPartialOrder _≡_ _⊂_
isStrictPartialOrder = ⊂.isPartialOrder⟶isStrictPartialOrder isPartialOrder


isDecStrictPartialOrder : IsDecStrictPartialOrder _≡_ _⊂_
isDecStrictPartialOrder = record
  { isStrictPartialOrder = isStrictPartialOrder
  ; _≟_                  = _≟_
  ; _<?_                 = ⊂.decidable _≟_ _⊆?_
  }
  where open Simple


mutual
  [A|A⊆_] : (B : Type) → Vec Type ⌈ B ⌉
  [A|A⊆ B ] = B ∷ [A|A⊂ B ]

  [A|A⊂_] : (B : Type) → Vec Type ⌊ B ⌋
  [A|A⊂ el  B ] = []
  [A|A⊂ B ⇒ C ] = [A|A⊆ B ] ++ [A|A⊆ C ]
  [A|A⊂ B ⇐ C ] = [A|A⊆ B ] ++ [A|A⊆ C ]
  [A|A⊂ B ⇚ C ] = [A|A⊆ B ] ++ [A|A⊆ C ]
  [A|A⊂ B ⇛ C ] = [A|A⊆ B ] ++ [A|A⊆ C ]
  [A|A⊂ B ⊗ C ] = [A|A⊆ B ] ++ [A|A⊆ C ]
  [A|A⊂ B ⊕ C ] = [A|A⊆ B ] ++ [A|A⊆ C ]


private
  lookup-++-raise : ∀ {a} {A : Set a} {m n}
                    (xs : Vec A m) (ys : Vec A n) i →
                    lookup (raise m i) (xs ++ ys) ≡ lookup i ys
  lookup-++-raise []       ys i = refl
  lookup-++-raise (x ∷ xs) ys i = lookup-++-raise xs ys i

  inl : ∀ {A B C}
      → Σ[ i ∈ Fin  ⌈ B ⌉          ]( A ≡ lookup i  [A|A⊆ B ]               )
      → Σ[ i ∈ Fin (⌈ B ⌉ + ⌈ C ⌉) ]( A ≡ lookup i ([A|A⊆ B ] ++ [A|A⊆ C ]) )
  inl {A} {B} {C} (i , p) = inject+ ⌈ C ⌉ i , P.trans p (sym (lookup-++-inject+ [A|A⊆ B ] [A|A⊆ C ] i))

  inr : ∀ {A B C}
      → Σ[ i ∈ Fin          ⌈ C ⌉  ]( A ≡ lookup i               [A|A⊆ C ]  )
      → Σ[ i ∈ Fin (⌈ B ⌉ + ⌈ C ⌉) ]( A ≡ lookup i ([A|A⊆ B ] ++ [A|A⊆ C ]) )
  inr {A} {B} {C} (i , p) = raise   ⌈ B ⌉ i , P.trans p (sym (lookup-++-raise   [A|A⊆ B ] [A|A⊆ C ] i))


mutual
  [A|A⊆B]-correct : ∀ {A B} → A ⊆ B → Σ[ i ∈ Fin ⌈ B ⌉ ]( A ≡ lookup i [A|A⊆ B ] )
  [A|A⊆B]-correct {A} {B} A⊆B with A ≟ B
  ...| yes A=B = zero , A=B
  ...| no  A≠B with [A|A⊂B]-correct (A⊆B , A≠B)
  ...| (i , p) = suc i , p

  [A|A⊂B]-correct : ∀ {A B} → A ⊂ B → Σ[ i ∈ Fin ⌊ B ⌋ ]( A ≡ lookup i [A|A⊂ B ] )
  [A|A⊂B]-correct {B = el  B} A⊂elB = ⊥-elim (A⊄elB A⊂elB)
  [A|A⊂B]-correct {B = B ⇒ C} A⊂B⇒C with ⇒-inj-⊂ A⊂B⇒C
  ...| inj₁ A⊆B = inl ([A|A⊆B]-correct A⊆B)
  ...| inj₂ A⊆C = inr ([A|A⊆B]-correct A⊆C)
  [A|A⊂B]-correct {B = B ⇐ C} A⊂B⇐C with ⇐-inj-⊂ A⊂B⇐C
  ...| inj₁ A⊆B = inl ([A|A⊆B]-correct A⊆B)
  ...| inj₂ A⊆C = inr ([A|A⊆B]-correct A⊆C)
  [A|A⊂B]-correct {B = B ⇚ C} A⊂B⇚C with ⇚-inj-⊂ A⊂B⇚C
  ...| inj₁ A⊆B = inl ([A|A⊆B]-correct A⊆B)
  ...| inj₂ A⊆C = inr ([A|A⊆B]-correct A⊆C)
  [A|A⊂B]-correct {B = B ⇛ C} A⊂B⇛C with ⇛-inj-⊂ A⊂B⇛C
  ...| inj₁ A⊆B = inl ([A|A⊆B]-correct A⊆B)
  ...| inj₂ A⊆C = inr ([A|A⊆B]-correct A⊆C)
  [A|A⊂B]-correct {B = B ⊗ C} A⊂B⊗C with ⊗-inj-⊂ A⊂B⊗C
  ...| inj₁ A⊆B = inl ([A|A⊆B]-correct A⊆B)
  ...| inj₂ A⊆C = inr ([A|A⊆B]-correct A⊆C)
  [A|A⊂B]-correct {B = B ⊕ C} A⊂B⊕C with ⊕-inj-⊂ A⊂B⊕C
  ...| inj₁ A⊆B = inl ([A|A⊆B]-correct A⊆B)
  ...| inj₂ A⊆C = inr ([A|A⊆B]-correct A⊆C)
