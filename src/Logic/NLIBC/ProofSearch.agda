--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------


open import Category.Monad   using (module RawMonadPlus; RawMonadPlus)
open import Data.List        using (List; foldr; map; _++_; _∷_; []; concat)
open import Data.List.Any    using (any)
open import Data.Nat         using (ℕ; suc; zero; _+_)
open import Data.Product     using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; trans; cong; subst)


module Logic.NLIBC.ProofSearch
  {ℓ} (Atom : Set ℓ) (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)) where


open import Logic.NLIBC.Type              Atom as T; open T.DecEq _≟-Atom_
open import Logic.NLIBC.Structure         Atom as S; open S.DecEq _≟-Atom_
open import Logic.NLIBC.Structure.Context Atom as C
open import Logic.NLIBC.Sequent         Atom as J; open J.DecEq _≟-Atom_
open import Logic.NLIBC.Base              Atom


focus : (Γ : Structure) → List (∃₂ (λ (Γ′ : Context) (Δ : Structure) → Γ′ [ Δ ] ≡ Γ))
focus (·  p  ·) = ([] , · p · , refl) ∷ []
focus (Γ₁ ∙ Γ₂) =
      ([] , Γ₁ ∙ Γ₂ , refl) ∷
      map (λ {(Γ₁′ , Δ , p) → Γ₁′ <∙ Γ₂ , Δ , cong (_∙ Γ₂) p}) (focus Γ₁) ++
      map (λ {(Γ₂′ , Δ , p) → Γ₁ ∙> Γ₂′ , Δ , cong (Γ₁ ∙_) p}) (focus Γ₂)
focus     Γ     = []


focus₁ : (Γ : Structure) → List (∃₂ (λ (Γ′ : Context₁) (Δ : Structure) → Γ′ [ Δ ] ≡ Γ))
focus₁ Γ = ([] , Γ , refl) ∷ focus′ Γ
  where
    focus′ : (Γ : Structure) → List (∃₂ (λ (Γ′ : Context₁) (Δ : Structure) → Γ′ [ Δ ] ≡ Γ))
    focus′ (Γ₁ ∙ Γ₂) =
      map (λ {(Γ₁′ , Δ , p) → Γ₁′ <∙ Γ₂ , Δ , cong (_∙ Γ₂) p}) (focus₁ Γ₁) ++
      map (λ {(Γ₂′ , Δ , p) → Γ₁ ∙> Γ₂′ , Δ , cong (Γ₁ ∙_) p}) (focus₁ Γ₂)
    focus′     Γ     = []


trace : (Γ : Structure) → List (∃ (λ Γ′ → λx Γ′ [x] ≡ Γ))
trace I             = ([] , refl) ∷ []
trace ((B ∙ p) ∙ Γ) = map (λ {(Γ′ , pr) → p ∙> Γ′ , cong (λ Γ′ → ((B ∙ p) ∙ Γ′)) pr}) (trace Γ)
trace ((C ∙ Γ) ∙ r) = map (λ {(Γ′ , pr) → Γ′ <∙ r , cong (λ Γ′ → ((C ∙ Γ′) ∙ r)) pr}) (trace Γ)
trace _             = []


-- Compute the number of logical connectives
connᵗ : Type → ℕ
connᵗ (el  p) = 1
connᵗ (p ⇒ q) = suc (connᵗ p + connᵗ q)
connᵗ (q ⇐ p) = suc (connᵗ p + connᵗ q)
connᵗ (p ⇨ q) = suc (connᵗ p + connᵗ q)
connᵗ (q ⇦ p) = suc (connᵗ p + connᵗ q)

connˢ : Structure → ℕ
connˢ · p · = connᵗ p
connˢ (Γ₁ ∙ Γ₂) = connˢ Γ₁ + connˢ Γ₂
connˢ (Γ₁ ∘ Γ₂) = connˢ Γ₁ + connˢ Γ₂
connˢ I = 0
connˢ B = 0
connˢ C = 0

connʲ : Sequent → ℕ
connʲ (Γ ⊢ p) = connˢ Γ + connᵗ p


findAll : (J : Sequent) → List (NL J)
findAll J = search (connʲ J) J
  where
  open RawMonadPlus Data.List.monadPlus using (∅; _∣_; return; _<$>_) renaming (_⊛_ to _<*>_)

  search : (n : ℕ) (J : Sequent) → List (NL J)
  search n J =
    {- composition -} check-ax        n J ∣ check-⇒ᴿ/⇐ᴿ n J ∣ check-⇒ᴸ/⇐ᴸ n J ∣
    {-   scoping   -} check-⇦ᴸλ       n J ∣ check-⇨ᴿλ   n J ∣
    {-   gapping   -} check-⇨ᴿgᴸ/⇨ᴿgᴿ n J
    where
    check-ax : (n : ℕ) (J : Sequent) → List (NL J)
    check-ax _ (· p · ⊢ q) with p ≟-Type q
    ... | yes p=q rewrite p=q = return ax
    ... | no  p≠q             = ∅
    check-ax _ _ = ∅

    check-⇒ᴿ/⇐ᴿ : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇒ᴿ/⇐ᴿ (suc n) (Γ ⊢ p ⇒ q) = ⇒ᴿ <$> search n (· p · ∙ Γ ⊢ q)
    check-⇒ᴿ/⇐ᴿ (suc n) (Γ ⊢ q ⇐ p) = ⇐ᴿ <$> search n (Γ ∙ · p · ⊢ q)
    check-⇒ᴿ/⇐ᴿ _ _ = ∅

    check-⇒ᴸ/⇐ᴸ : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇒ᴸ/⇐ᴸ (suc n) (Γ ⊢ r) = concat (map check-⇒ᴸ/⇐ᴸ′ (focus Γ))
      where
      check-⇒ᴸ/⇐ᴸ′ : (∃₂ (λ (Σ : Context) (Δ : Structure) → Σ [ Δ ] ≡ Γ)) → List (Γ ⊢NL r)
      check-⇒ᴸ/⇐ᴸ′ (Σ , Δ ∙ · p ⇒ q · , pr)
        = (λ f g → subst (_⊢NL r) pr (⇒ᴸ Σ f g)) <$> search n (Δ ⊢ p) <*> search n (Σ [ · q · ] ⊢ r)
      check-⇒ᴸ/⇐ᴸ′ (Σ , · q ⇐ p · ∙ Δ , pr)
        = (λ f g → subst (_⊢NL r) pr (⇐ᴸ Σ f g)) <$> search n (Δ ⊢ p) <*> search n (Σ [ · q · ] ⊢ r)
      check-⇒ᴸ/⇐ᴸ′ _ = ∅
    check-⇒ᴸ/⇐ᴸ _ _ = ∅

    check-⇨ᴿ/⇦ᴿ : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇨ᴿ/⇦ᴿ (suc n) (Γ ⊢ p ⇨ q) = ⇨ᴿ <$> search n (· p · ∘ Γ ⊢ q)
    check-⇨ᴿ/⇦ᴿ (suc n) (Γ ⊢ q ⇦ p) = ⇦ᴿ <$> search n (Γ ∘ · p · ⊢ q)
    check-⇨ᴿ/⇦ᴿ _ _ = ∅

    -- QR up
    check-⇦ᴸλ : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇦ᴸλ (suc n) (Γ ⊢ r) = concat (map check-⇦ᴸλ′ (focus Γ))
      where
      check-⇦ᴸλ′ : (∃₂ (λ (Σ : Context) (Γ′ : Structure) → Σ [ Γ′ ] ≡ Γ)) → List (Γ ⊢NL r)
      check-⇦ᴸλ′ (Σ , Γ′ , pr₁) = concat (map check-⇦ᴸλ″ (focus₁ Γ′))
        where
        check-⇦ᴸλ″ : (∃₂ (λ (Γ″ : Context₁) (Δ : Structure) → Γ″ [ Δ ] ≡ Γ′)) → List (Γ ⊢NL r)
        check-⇦ᴸλ″ (Γ″ , · q ⇦ p · , pr₂) =
          let pr = trans (cong (Σ [_]) pr₂) pr₁ in
          (λ f g → subst (_⊢NL r) pr (⇦ᴸλ Σ Γ″ f g))
            <$> search n (λx Γ″ [x] ⊢ p)
            <*> search n (Σ [ · q · ] ⊢ r)
        check-⇦ᴸλ″ _ = ∅
    check-⇦ᴸλ _ _ = ∅

    -- QR to the top
    check-⇦ᴸλ′ : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇦ᴸλ′ (suc n) (Γ ⊢ r) = concat (map check-⇦ᴸλ″ (focus₁ Γ))
      where
      check-⇦ᴸλ″ : (∃₂ (λ (Γ′ : Context₁) (Δ : Structure) → Γ′ [ Δ ] ≡ Γ)) → List (Γ ⊢NL r)
      check-⇦ᴸλ″ (Γ′ , · q ⇦ p · , pr) =
        (λ f g → subst (_⊢NL r) pr (⇦ᴸλ [] Γ′ f g))
          <$> search n (λx Γ′ [x] ⊢ p)
          <*> search n (· q · ⊢ r)
      check-⇦ᴸλ″ _ = ∅
    check-⇦ᴸλ′ _ _ = ∅

    -- QR down
    check-⇨ᴿλ : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇨ᴿλ (suc n) (Γ ⊢ p ⇨ q) = concat (map check-⇨ᴿλ′ (trace Γ))
      where
      check-⇨ᴿλ′ : ∃ (λ Γ′ → λx Γ′ [x] ≡ Γ) → List (Γ ⊢NL p ⇨ q)
      check-⇨ᴿλ′ (Γ′ , pr) =
        (λ f → subst (_⊢NL _) pr (⇨ᴿλ Γ′ f)) <$> search n (Γ′ [ · p · ] ⊢ q)
    check-⇨ᴿλ _ _ = ∅

    -- gapping
    check-⇨ᴿgᴸ/⇨ᴿgᴿ : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇨ᴿgᴸ/⇨ᴿgᴿ (suc n) (Γ ⊢ q ⇨ r) = foldr _∣_ ∅ (map check-⇨ᴿgᴸ/⇨ᴿgᴿ′ (focus Γ))
      where
      check-⇨ᴿgᴸ/⇨ᴿgᴿ′ : (∃₂ (λ (Σ : Context) (Δ : Structure) → Σ [ Δ ] ≡ Γ)) → List (Γ ⊢NL q ⇨ r)
      check-⇨ᴿgᴸ/⇨ᴿgᴿ′ (Σ , · p · , pr) =
        (λ f → subst (_⊢NL _) pr (⇨ᴿgᴸ Σ f)) <$> search n (Σ [ · q · ∙ · p · ] ⊢ r) ∣
        (λ f → subst (_⊢NL _) pr (⇨ᴿgᴿ Σ f)) <$> search n (Σ [ · p · ∙ · q · ] ⊢ r)
      check-⇨ᴿgᴸ/⇨ᴿgᴿ′ _ =  ∅
    check-⇨ᴿgᴸ/⇨ᴿgᴿ _ _ = ∅

-- -}
-- -}
-- -}
-- -}
-- -}
