------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                                   using (_$_)
open import Category.Monad                             using (module RawMonad)
open import Data.Bool                                  using (Bool; true; false)
open import Data.Empty                                 using (⊥-elim)
open import Data.List                                  using (List; _++_)
open import Data.Product                               using (∃; ∃₂; Σ-syntax; _×_; _,_; ,_; proj₁; proj₂)
open import Data.Sum                                   using (_⊎_; inj₁; inj₂)
open import Data.Unit                                  using (⊤; tt)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable                 using (toWitness; toWitnessFalse; fromWitness; fromWitnessFalse)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl; sym; cong; trans; subst)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)


module Logic.Intuitionistic.Ordered.Lambek.SC.Decidable {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Ordered.Lambek.Type         Univ as T
open import Logic.Intuitionistic.Ordered.Lambek.Type.Subtype Univ as ⊆
open import Logic.Intuitionistic.Ordered.Lambek.Type.Context Univ as C
open import Logic.Intuitionistic.Ordered.Lambek.SC.Judgement Univ as J
open import Logic.Intuitionistic.Ordered.Lambek.SC.Base      Univ as B
open C.Simple using (_[_]; _<_>; <>-def; <>-assoc)


data Contextᴺ : (Γ : Context) → Set ℓ where
  []   : Contextᴺ []
  _⊗>_ : ∀ (A : Type) {Γ} (Γᴺ : Contextᴺ Γ) → Contextᴺ (A ⊗> Γ)
  _<⊗_ : ∀ {Γ} (Γᴺ : Contextᴺ Γ) (A : Type) → Contextᴺ (Γ <⊗ A)
  _⇒>_ : ∀ (A : Type) {Γ} (Γᴺ : Contextᴺ Γ) → Contextᴺ (A ⇒> Γ)
  _<⇐_ : ∀ {Γ} (Γᴺ : Contextᴺ Γ) (A : Type) → Contextᴺ (Γ <⇐ A)

_<_>ᴺ : ∀ {Γ₁ Γ₂} (Γ₁ᴺ : Contextᴺ Γ₁) (Γ₂ᴺ : Contextᴺ Γ₂) → Contextᴺ (Γ₁ < Γ₂ >)
[]        < Γ₂ >ᴺ = Γ₂
(A ⊗> Γ₁) < Γ₂ >ᴺ = A ⊗> (Γ₁ < Γ₂ >ᴺ)
(Γ₁ <⊗ A) < Γ₂ >ᴺ = (Γ₁ < Γ₂ >ᴺ) <⊗ A
(A ⇒> Γ₁) < Γ₂ >ᴺ = A ⇒> (Γ₁ < Γ₂ >ᴺ)
(Γ₁ <⇐ A) < Γ₂ >ᴺ = (Γ₁ < Γ₂ >ᴺ) <⇐ A


⊢ᴺ→Contextᴺ : ∀ {Γ} (x : NL ⊢ᴺ Γ) → Contextᴺ Γ
⊢ᴺ→Contextᴺ  neg-[]        = []
⊢ᴺ→Contextᴺ (neg-⊗⇒ _ x y) = _ ⊗> (⊢ᴺ→Contextᴺ x < _ ⇒> ⊢ᴺ→Contextᴺ y >ᴺ)
⊢ᴺ→Contextᴺ (neg-⊗⇐ _ x y) = (⊢ᴺ→Contextᴺ x < ⊢ᴺ→Contextᴺ y <⇐ _ >ᴺ) <⊗ _

lemma : ∀ {AC B D} (f : NL AC ⊢ B ⊗ D)
      → Σ[ A  ∈ _ ]
        Σ[ C  ∈ _ ]
        Σ[ h₁ ∈ NL A ⊢ B ]
        Σ[ h₂ ∈ NL C ⊢ D ]
        (
          Σ[ p₁ ∈ AC ≡ A ⊗ C ]
            f ≅ mon-⊗ h₁ h₂
        )
        ⊎
        (
          Σ[ Γ  ∈ _ ]
          Σ[ x  ∈ NL ⊢ᴺ Γ ]
          Σ[ p₁ ∈ AC ≡ Γ [ A ⊗ C ] ]
          Σ[ p₂ ∈ Γ ≢ [] ]
          (_≅_
            {A = NL AC ⊢ B ⊗ D}
              f
            {B = NL Γ [ A ⊗ C ] ⊢ B ⊗ D}
              (contᴺ (mon-⊗ h₁ h₂) x refl tt (fromWitnessFalse p₂)))
        )
lemma (mon-⊗ h₁ h₂) = , , (h₁ , h₂ , inj₁ (refl , refl))
lemma (contᴺ {Γ} f x p₁ p₂ p₃) with lemma f
...| A , C , h₁ , h₂ , inj₁ (         p₄ ,      p₆)
   = A , C , h₁ , h₂ , inj₂ (Γ  , x , trans p₁ (cong (λ A → Γ [ A ]) p₄)
                                    , toWitnessFalse p₃
                                    , {!!}
                                    )
...| A , C , h₁ , h₂ , inj₂ (Γ′ , y , p₄ , p₅ , p₆) = {!!}
lemma (contᴾ f x p₁ p₂ p₃) = {!!}

{-
        Σ[ A  ∈ _                          ]
        Σ[ C  ∈ _                          ]
        Σ[ Γ  ∈ _                          ]
        Σ[ p₁ ∈ AC ≡ Γ [ A ⊗ C ]           ]
        Σ[ f₁ ∈ NL A ⊢ B                   ]
        Σ[ f₂ ∈ NL C ⊢ D                   ]
        Σ[ x  ∈ NL ⊢ᴺ Γ                    ]
        {!!}
        ⊎
        {!!}
lemma f = {!!}
lemma (mon-⊗ f₁ f₂)        = , , , (refl , f₁ , f₂ , neg-[] , refl)
lemma {AC} {B} {D} (contᴺ {Γ} f x p₁ p₂ p₃) with lemma f
...| A  , C  , Γ′ , p₄ , f₁ , f₂ , y , p₅ with is-[]? (Γ < Γ′ >)
...| yes Γ<Γ′>=[] = {!!}
...| no  Γ<Γ′>≠[] = A , C , Γ < Γ′ > , p₆ , f₁ , f₂ , transᴺ′ x y , {!p₅!}
  where
    p₆ : AC ≡ (Γ < Γ′ >) [ A ⊗ C ]
    p₆ = trans p₁ (trans (cong (λ A → Γ [ A ]) p₄) (sym (<>-def Γ Γ′ (A ⊗ C))))

--= A , C , Γ < Γ′ > , trans p₁ (trans (cong (λ A → Γ [ A ]) p₄) (sym (<>-def Γ Γ′ (A ⊗ C))))
--      , f₁ , f₂ , transᴺ′ x y , {!!}
lemma (contᴾ f x p₁ p₂ p₃) = {!!}
-}
{-
first-⊗ : ∀ {Γ} (x : NL ⊢ᴺ Γ) → Γ ≢ [] → ∃₂ (λ A Γ′ → Γ ≡ A ⊗> Γ′ ⊎ Γ ≡ Γ′ <⊗ A)
first-⊗  neg-[]        Γ≠[] = ⊥-elim (Γ≠[] refl)
first-⊗ (neg-⊗⇒ _ _ _) Γ≠[] = , , inj₁ refl
first-⊗ (neg-⊗⇐ _ _ _) Γ≠[] = , , inj₂ refl

last-⇒⇐ : ∀ {Γ} (x : NL ⊢ᴺ Γ) → Γ ≢ [] → ∃₂ (λ A Γ′ → Γ ≡ Γ′ < A ⇒> [] > ⊎ Γ ≡ Γ′ < [] <⇐ A >)
last-⇒⇐ neg-[] Γ≠[] = ⊥-elim (Γ≠[] refl)
last-⇒⇐ (neg-⊗⇒ {Γ} {Δ} {B} {C} _ _ y) Γ≠[] with is-[]? Δ
...| yes Δ=[] rewrite Δ=[] = _ , _ ⊗> Γ , inj₁ refl
...| no  Δ≠[] with last-⇒⇐ y Δ≠[]
...| A , Δ′                 , inj₁ Δ=Δ′<A⇒>[]> rewrite Δ=Δ′<A⇒>[]>
   = A , B ⊗> Γ < C ⇒> Δ′ > , inj₁ (cong (λ Γ → B ⊗> Γ) (sym (<>-assoc Γ (C ⇒> Δ′) (A ⇒> []))))
...| A , Δ′                 , inj₂ Δ=Δ′<[]<⇐A> rewrite Δ=Δ′<[]<⇐A>
   = A , B ⊗> Γ < C ⇒> Δ′ > , inj₂ (cong (λ Γ → B ⊗> Γ) (sym (<>-assoc Γ (C ⇒> Δ′) ([] <⇐ A))))
last-⇒⇐ (neg-⊗⇐ {Γ} {Δ} {B} {C} _ _ y) Γ≠[] with is-[]? Δ
...| yes Δ=[] rewrite Δ=[] = _ , Γ <⊗ _ , inj₂ refl
...| no  Δ≠[] with last-⇒⇐ y Δ≠[]
...| A ,     Δ′             , inj₁ Δ=Δ′<A⇒>[]> rewrite Δ=Δ′<A⇒>[]>
   = A , Γ < Δ′ <⇐ C > <⊗ B , inj₁ (cong (λ Γ → Γ <⊗ B) (sym (<>-assoc Γ (Δ′ <⇐ C) (A ⇒> []))))
...| A ,     Δ′             , inj₂ Δ=Δ′<[]<⇐A> rewrite Δ=Δ′<[]<⇐A>
   = A , Γ < Δ′ <⇐ C > <⊗ B , inj₂ (cong (λ Γ → Γ <⊗ B) (sym (<>-assoc Γ (Δ′ <⇐ C) ([] <⇐ A))))
-}





{-# NO_TERMINATION_CHECK #-}
dec_ : (J : Judgement) → Dec (NL J)
dec J = {!!}
