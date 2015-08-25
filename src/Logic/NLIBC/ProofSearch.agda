--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------


open import Category.Monad   using (module RawMonadPlus; RawMonadPlus)
open import Data.Maybe       using (Maybe; From-just; from-just)
open import Data.List        using (List; foldr; map; _++_; _∷_; [])
open import Data.List.Any    using (any)
open import Data.Product     using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; trans; cong; subst)


module Logic.NLIBC.ProofSearch
  {ℓ} (Atom : Set ℓ) (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)) where


open import Logic.NLIBC.Type              Atom as T; open T.DecEq _≟-Atom_
open import Logic.NLIBC.Structure         Atom as S; open S.DecEq _≟-Atom_
open import Logic.NLIBC.Structure.Context Atom as C
open import Logic.NLIBC.Judgement         Atom as J; open J.DecEq _≟-Atom_
open import Logic.NLIBC.Base              Atom



focus : (Γ : Structure) → List (∃₂ (λ (Γ′ : Context) (Δ : Structure) → Γ′ [ Δ ] ≡ Γ))
focus Γ = ([] , Γ , refl) ∷ focus′ Γ
  where
    focus′ : (Γ : Structure) → List (∃₂ (λ (Γ′ : Context) (Δ : Structure) → Γ′ [ Δ ] ≡ Γ))
    focus′ (Γ₁ ∙ Γ₂) =
      map (λ {(Γ₁′ , Δ , p) → Γ₁′ <∙ Γ₂ , Δ , cong (_∙ Γ₂) p}) (focus Γ₁) ++
      map (λ {(Γ₂′ , Δ , p) → Γ₁ ∙> Γ₂′ , Δ , cong (Γ₁ ∙_) p}) (focus Γ₂)
    focus′ (Γ₁ ∘ Γ₂) =
      map (λ {(Γ₁′ , Δ , p) → Γ₁′ <∘ Γ₂ , Δ , cong (_∘ Γ₂) p}) (focus Γ₁) ++
      map (λ {(Γ₂′ , Δ , p) → Γ₁ ∘> Γ₂′ , Δ , cong (Γ₁ ∘_) p}) (focus Γ₂)
    focus′     Γ     = []


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


{-# TERMINATING #-}
search : {Mon : Set ℓ → Set ℓ} {{monadPlus : RawMonadPlus Mon}} (J : Judgement) → Mon (NL J)
search {Mon} {{monadPlus}} J =
  check-ax    J ∣ check-⇒ᴿ/⇐ᴿ J ∣ check-⇒ᴸ/⇐ᴸ J ∣
  check-⇨ᴿ/⇦ᴿ J ∣ check-⇦ᴸλ′  J ∣ check-⇨ᴿλ′  J
  where
  open RawMonadPlus monadPlus using (∅; _∣_; return; _>>=_; _<$>_) renaming (_⊛_ to _<*>_)

  check-ax : (J : Judgement) → Mon (NL J)
  check-ax (· p · ⊢ q) with p ≟-Type q
  ... | yes p=q rewrite p=q = return ax
  ... | no  p≠q             = ∅
  check-ax _ = ∅

  check-⇒ᴿ/⇐ᴿ : (J : Judgement) → Mon (NL J)
  check-⇒ᴿ/⇐ᴿ (Γ ⊢ p ⇒ q) = ⇒ᴿ <$> search (· p · ∙ Γ ⊢ q)
  check-⇒ᴿ/⇐ᴿ (Γ ⊢ q ⇐ p) = ⇐ᴿ <$> search (Γ ∙ · p · ⊢ q)
  check-⇒ᴿ/⇐ᴿ _ = ∅

  check-⇒ᴸ/⇐ᴸ : (J : Judgement) → Mon (NL J)
  check-⇒ᴸ/⇐ᴸ (Γ ⊢ r) = foldr _∣_ ∅ (map check-⇒ᴸ/⇐ᴸ′ (focus Γ))
    where
    check-⇒ᴸ/⇐ᴸ′ : (∃₂ (λ (Σ : Context) (Δ : Structure) → Σ [ Δ ] ≡ Γ)) → Mon (Γ ⊢NL r)
    check-⇒ᴸ/⇐ᴸ′ (Σ , Δ ∙ · p ⇒ q · , pr)
      = (λ f g → subst (_⊢NL r) pr (⇒ᴸ Σ f g)) <$> search (Δ ⊢ p) <*> search (Σ [ · q · ] ⊢ r)
    check-⇒ᴸ/⇐ᴸ′ (Σ , · q ⇐ p · ∙ Δ , pr)
      = (λ f g → subst (_⊢NL r) pr (⇐ᴸ Σ f g)) <$> search (Δ ⊢ p) <*> search (Σ [ · q · ] ⊢ r)
    check-⇒ᴸ/⇐ᴸ′ _ = ∅

  check-⇨ᴿ/⇦ᴿ : (J : Judgement) → Mon (NL J)
  check-⇨ᴿ/⇦ᴿ (Γ ⊢ p ⇨ q) = ⇨ᴿ <$> search (· p · ∘ Γ ⊢ q)
  check-⇨ᴿ/⇦ᴿ (Γ ⊢ q ⇦ p) = ⇦ᴿ <$> search (Γ ∘ · p · ⊢ q)
  check-⇨ᴿ/⇦ᴿ _ = ∅

  check-⇨ᴸ/⇦ᴸ : (J : Judgement) → Mon (NL J)
  check-⇨ᴸ/⇦ᴸ (Γ ⊢ r) = foldr _∣_ ∅ (map check-⇨ᴸ/⇦ᴸ′ (focus Γ))
    where
    check-⇨ᴸ/⇦ᴸ′ : (∃₂ (λ (Σ : Context) (Δ : Structure) → Σ [ Δ ] ≡ Γ)) → Mon (Γ ⊢NL r)
    check-⇨ᴸ/⇦ᴸ′ (Σ , Δ ∘ · p ⇨ q · , pr)
      = (λ f g → subst (_⊢NL r) pr (⇨ᴸ Σ f g)) <$> search (Δ ⊢ p) <*> search (Σ [ · q · ] ⊢ r)
    check-⇨ᴸ/⇦ᴸ′ (Σ , · q ⇦ p · ∘ Δ , pr)
      = (λ f g → subst (_⊢NL r) pr (⇦ᴸ Σ f g)) <$> search (Δ ⊢ p) <*> search (Σ [ · q · ] ⊢ r)
    check-⇨ᴸ/⇦ᴸ′ _ = ∅

  -- QR upwards
  check-⇦ᴸλ : (J : Judgement) → Mon (NL J)
  check-⇦ᴸλ (Γ ⊢ r) = foldr _∣_ ∅ (map check-⇦ᴸλ′ (focus Γ))
    where
    check-⇦ᴸλ′ : (∃₂ (λ (Σ : Context) (Γ′ : Structure) → Σ [ Γ′ ] ≡ Γ)) → Mon (Γ ⊢NL r)
    check-⇦ᴸλ′ (Σ , Γ′ , pr₁) = foldr _∣_ ∅ (map check-⇦ᴸλ″ (focus₁ Γ′))
      where
      check-⇦ᴸλ″ : (∃₂ (λ (Γ″ : Context₁) (Δ : Structure) → Γ″ [ Δ ] ≡ Γ′)) → Mon (Γ ⊢NL r)
      check-⇦ᴸλ″ (Γ″ , · q ⇦ p · , pr₂) =
        let pr = trans (cong (Σ [_]) pr₂) pr₁ in
        search (λx Γ″ [x] ⊢ p)   >>= λ f →
        search (Σ [ · q · ] ⊢ r) >>= λ g →
        return (subst (_⊢NL r) pr (⇦ᴸλ Σ Γ″ f g))
      check-⇦ᴸλ″ _ = ∅

  -- QR to the top
  check-⇦ᴸλ′ : (J : Judgement) → Mon (NL J)
  check-⇦ᴸλ′ (Γ ⊢ r) = foldr _∣_ ∅ (map check-⇦ᴸλ″ (focus₁ Γ))
    where
    check-⇦ᴸλ″ : (∃₂ (λ (Γ′ : Context₁) (Δ : Structure) → Γ′ [ Δ ] ≡ Γ)) → Mon (Γ ⊢NL r)
    check-⇦ᴸλ″ (Γ′ , · q ⇦ p · , pr) =
      search (λx Γ′ [x] ⊢ p) >>= λ f →
      search (· q · ⊢ r)     >>= λ g →
      return (subst (_⊢NL r) pr (⇦ᴸλ [] Γ′ f g))
    check-⇦ᴸλ″ _ = ∅

  -- QR downwards
  check-⇨ᴿλ : (J : Judgement) → Mon (NL J)
  check-⇨ᴿλ (Γ ⊢ r) = foldr _∣_ ∅ (map check-⇨ᴿλ′ (focus Γ))
    where
    check-⇨ᴿλ′ : (∃₂ (λ (Σ : Context) (Γ′ : Structure) → Σ [ Γ′ ] ≡ Γ)) → Mon (Γ ⊢NL r)
    check-⇨ᴿλ′  (Σ , Δ ∘ Γ′ , pr₁) = foldr _∣_ ∅ (map check-⇨ᴿλ″ (trace Γ′))
      where
      check-⇨ᴿλ″ : ∃ (λ Γ″ → λx Γ″ [x] ≡ Γ′) → Mon (Γ ⊢NL r)
      check-⇨ᴿλ″ (Γ″ , pr₂) =
        let pr = trans (cong (λ Γ′ → Σ [ Δ ∘ Γ′ ]) pr₂) pr₁ in
        search (Σ [ Γ″ [ Δ ] ] ⊢ r) >>= λ f →
        return (subst (_⊢NL r) pr (down Σ Γ″ f))
    check-⇨ᴿλ′ _ = ∅

  -- QR all the way down
  check-⇨ᴿλ′ : (J : Judgement) → Mon (NL J)
  check-⇨ᴿλ′ (Δ ∘ Γ ⊢ r) = foldr _∣_ ∅ (map check-⇨ᴿλ″ (trace Γ))
    where
    check-⇨ᴿλ″ : ∃ (λ Γ′ → λx Γ′ [x] ≡ Γ) → Mon (Δ ∘ Γ ⊢NL r)
    check-⇨ᴿλ″ (Γ′ , pr) =
      search (Γ′ [ Δ ] ⊢ r) >>= λ f →
      return (subst (_⊢NL r) (cong (Δ ∘_) pr) (down [] Γ′ f))
  check-⇨ᴿλ′ _ = ∅

  -- QR downwards freely
  check-IBC : (J : Judgement) → Mon (NL J)
  check-IBC (Γ ⊢ s) = foldr _∣_ ∅ (map check-IBC′ (focus Γ))
    where
    check-IBC′ : (∃₂ (λ (Σ : Context) (Γ′ : Structure) → Σ [ Γ′ ] ≡ Γ)) → Mon (Γ ⊢NL s)
    check-IBC′ (Σ , p ∘ I , pr) =
      (λ f → subst (_⊢NL s) pr (Iₑ Σ f)) <$> search (Σ [ p ] ⊢ s)
    check-IBC′ (Σ , q ∘ ((B ∙ p) ∙ r) , pr) =
      (λ f → subst (_⊢NL s) pr (Bₑ Σ f)) <$> search (Σ [ p ∙ (q ∘ r) ] ⊢ s)
    check-IBC′ (Σ , p ∘ ((C ∙ q) ∙ r) , pr) =
      (λ f → subst (_⊢NL s) pr (Cₑ Σ f)) <$> search (Σ [ (p ∘ q) ∙ r ] ⊢ s)
    check-IBC′ _ = ∅


findMaybe : (J : Judgement) → Maybe (NL J)
findMaybe = search {{Data.Maybe.monadPlus}}

find : (J : Judgement) → From-just (NL J) (findMaybe J)
find J = from-just (findMaybe J)

findAll : (J : Judgement) → List (NL J)
findAll = search {{Data.List.monadPlus}}
