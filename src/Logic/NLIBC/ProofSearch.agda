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
    {- composition -} check-ax        n J ∣ check-⇒R/⇐R n J ∣ check-⇒L/⇐L n J ∣
    {-   scoping   -} check-⇦Lλ       n J ∣ check-⇨Rλ   n J ∣
    {-   gapping   -} check-⇨RgL/⇨RgR n J
    where
    check-ax : (n : ℕ) (J : Sequent) → List (NL J)
    check-ax _ (· p · ⊢ q) with p ≟-Type q
    ... | yes p=q rewrite p=q = return ax
    ... | no  p≠q             = ∅
    check-ax _ _ = ∅

    check-⇒R/⇐R : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇒R/⇐R (suc n) (Γ ⊢ p ⇒ q) = ⇒R <$> search n (· p · ∙ Γ ⊢ q)
    check-⇒R/⇐R (suc n) (Γ ⊢ q ⇐ p) = ⇐R <$> search n (Γ ∙ · p · ⊢ q)
    check-⇒R/⇐R _ _ = ∅

    check-⇒L/⇐L : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇒L/⇐L (suc n) (Γ ⊢ r) = concat (map check-⇒L/⇐L′ (focus Γ))
      where
      check-⇒L/⇐L′ : (∃₂ (λ (Σ : Context) (Δ : Structure) → Σ [ Δ ] ≡ Γ)) → List (Γ ⊢NL r)
      check-⇒L/⇐L′ (Σ , Δ ∙ · p ⇒ q · , pr)
        = (λ f g → subst (_⊢NL r) pr (⇒L Σ f g)) <$> search n (Δ ⊢ p) <*> search n (Σ [ · q · ] ⊢ r)
      check-⇒L/⇐L′ (Σ , · q ⇐ p · ∙ Δ , pr)
        = (λ f g → subst (_⊢NL r) pr (⇐L Σ f g)) <$> search n (Δ ⊢ p) <*> search n (Σ [ · q · ] ⊢ r)
      check-⇒L/⇐L′ _ = ∅
    check-⇒L/⇐L _ _ = ∅

    check-⇨R/⇦R : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇨R/⇦R (suc n) (Γ ⊢ p ⇨ q) = ⇨R <$> search n (· p · ∘ Γ ⊢ q)
    check-⇨R/⇦R (suc n) (Γ ⊢ q ⇦ p) = ⇦R <$> search n (Γ ∘ · p · ⊢ q)
    check-⇨R/⇦R _ _ = ∅

    -- QR up
    check-⇦Lλ : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇦Lλ (suc n) (Γ ⊢ r) = concat (map check-⇦Lλ′ (focus Γ))
      where
      check-⇦Lλ′ : (∃₂ (λ (Σ : Context) (Γ′ : Structure) → Σ [ Γ′ ] ≡ Γ)) → List (Γ ⊢NL r)
      check-⇦Lλ′ (Σ , Γ′ , pr₁) = concat (map check-⇦Lλ″ (focus₁ Γ′))
        where
        check-⇦Lλ″ : (∃₂ (λ (Γ″ : Context₁) (Δ : Structure) → Γ″ [ Δ ] ≡ Γ′)) → List (Γ ⊢NL r)
        check-⇦Lλ″ (Γ″ , · q ⇦ p · , pr₂) =
          let pr = trans (cong (Σ [_]) pr₂) pr₁ in
          (λ f g → subst (_⊢NL r) pr (⇦Lλ Σ Γ″ f g))
            <$> search n (λx Γ″ [x] ⊢ p)
            <*> search n (Σ [ · q · ] ⊢ r)
        check-⇦Lλ″ _ = ∅
    check-⇦Lλ _ _ = ∅

    -- QR to the top
    check-⇦Lλ′ : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇦Lλ′ (suc n) (Γ ⊢ r) = concat (map check-⇦Lλ″ (focus₁ Γ))
      where
      check-⇦Lλ″ : (∃₂ (λ (Γ′ : Context₁) (Δ : Structure) → Γ′ [ Δ ] ≡ Γ)) → List (Γ ⊢NL r)
      check-⇦Lλ″ (Γ′ , · q ⇦ p · , pr) =
        (λ f g → subst (_⊢NL r) pr (⇦Lλ [] Γ′ f g))
          <$> search n (λx Γ′ [x] ⊢ p)
          <*> search n (· q · ⊢ r)
      check-⇦Lλ″ _ = ∅
    check-⇦Lλ′ _ _ = ∅

    -- QR down
    check-⇨Rλ : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇨Rλ (suc n) (Γ ⊢ p ⇨ q) = concat (map check-⇨Rλ′ (trace Γ))
      where
      check-⇨Rλ′ : ∃ (λ Γ′ → λx Γ′ [x] ≡ Γ) → List (Γ ⊢NL p ⇨ q)
      check-⇨Rλ′ (Γ′ , pr) =
        (λ f → subst (_⊢NL _) pr (⇨Rλ Γ′ f)) <$> search n (Γ′ [ · p · ] ⊢ q)
    check-⇨Rλ _ _ = ∅

    -- gapping
    check-⇨RgL/⇨RgR : (n : ℕ) (J : Sequent) → List (NL J)
    check-⇨RgL/⇨RgR (suc n) (Γ ⊢ q ⇨ r) = foldr _∣_ ∅ (map check-⇨RgL/⇨RgR′ (focus Γ))
      where
      check-⇨RgL/⇨RgR′ : (∃₂ (λ (Σ : Context) (Δ : Structure) → Σ [ Δ ] ≡ Γ)) → List (Γ ⊢NL q ⇨ r)
      check-⇨RgL/⇨RgR′ (Σ , · p · , pr) =
        (λ f → subst (_⊢NL _) pr (⇨RgL Σ f)) <$> search n (Σ [ · q · ∙ · p · ] ⊢ r) ∣
        (λ f → subst (_⊢NL _) pr (⇨RgR Σ f)) <$> search n (Σ [ · p · ∙ · q · ] ⊢ r)
      check-⇨RgL/⇨RgR′ _ =  ∅
    check-⇨RgL/⇨RgR _ _ = ∅

-- -}
-- -}
-- -}
-- -}
-- -}
