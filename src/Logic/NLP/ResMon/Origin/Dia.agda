--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Origin/Dia.agda
--------------------------------------------------------------------------------


open import Function                              using (id; flip; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)


module Logic.NLP.ResMon.Origin.Dia {ℓ} (Atom : Set ℓ) where


  open import Logic.Polarity
  open import Logic.NLP.Type                               Atom as T
  open import Logic.NLP.Type.Context.Polarised             Atom as TC
  open import Logic.NLP.ResMon.Sequent                   Atom
  open import Logic.NLP.ResMon.Sequent.Context.Polarised Atom as JC
  open import Logic.NLP.ResMon.Base                        Atom as NLPB


  data Origin {B} ( J : Contextʲ - ) (f : NLP J [ ◇ B ]ʲ) : Set ℓ where
       origin : ∀ {A}
                → (h : NLP A ⊢ B)
                → (f′ : ∀ {G} → NLP ◇ A ⊢ G → NLP J [ G ]ʲ)
                → (pr : f ≡ f′ (m◇ h))
                → Origin J f

  mutual
    view : ∀ {B} ( J : Contextʲ - ) (f : NLP J [ ◇ B ]ʲ) → Origin J f
    view (._ ⊢> [])       (m◇  f)   = origin f id refl

    view ((A <⊗ _) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
    view ((_ ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
    view (._ ⊢> (_ ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
    view (._ ⊢> (A <⇒ _)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
    view (._ ⊢> (_ ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
    view (._ ⊢> (A <⇐ _)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
    view (A <⊢ ._)        (r⊗⇒ f)   = go ((_ ⊗> A) <⊢ _)        f r⊗⇒
    view (._ ⊢> (_ ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
    view (._ ⊢> (A <⇒ _)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
    view ((_ ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
    view ((A <⊗ _) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
    view (._ ⊢> B)        (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> B))        f r⇒⊗
    view (A <⊢ ._)        (r⊗⇐ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇐
    view (._ ⊢> (_ ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
    view (._ ⊢> (A <⇐ _)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
    view ((_ ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
    view ((A <⊗ _) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
    view (._ ⊢> B)        (r⇐⊗ f)   = go (_ ⊢> (B <⇐ _))        f r⇐⊗
    -- cases for (□ , ◇)
    view (._ ⊢> (□> B))   (m□  f)   = go (_ ⊢> B)               f m□
    view ((◇> A) <⊢ ._)   (m◇  f)   = go (A <⊢ _)               f m◇
    view (._ ⊢> B)        (r□◇ f)   = go (_ ⊢> (□> B))          f r□◇
    view ((◇> A) <⊢ ._)   (r□◇ f)   = go (A <⊢ _)               f r□◇
    view (A <⊢ ._)        (r◇□ f)   = go ((◇> A) <⊢ _)          f r◇□
    view (._ ⊢> (□> B))   (r◇□ f)   = go (_ ⊢> B)               f r◇□

    private
      go : ∀ {B}
         → ( I : Contextʲ - ) (f : NLP I [ ◇ B ]ʲ)
         → { J : Contextʲ - } (g : ∀ {G} → NLP I [ G ]ʲ → NLP J [ G ]ʲ)
         → Origin J (g f)
      go I f {J} g with view I f
      ... | origin h f′ pr rewrite pr = origin h (g ∘ f′) refl
