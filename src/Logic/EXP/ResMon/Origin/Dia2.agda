--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Origin/Dia.agda
--------------------------------------------------------------------------------


open import Function                              using (id; flip; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)


module Logic.EXP.ResMon.Origin.Dia2 {ℓ} (Atom : Set ℓ) where


  open import Logic.Polarity
  open import Logic.EXP.Type                               Atom as T
  open import Logic.EXP.Type.Context.Polarised             Atom as TC
  open import Logic.EXP.ResMon.Judgement                   Atom
  open import Logic.EXP.ResMon.Judgement.Context.Polarised Atom as JC
  open import Logic.EXP.ResMon.Base                        Atom as EXPB


  data Origin {A} ( J : Contextᴶ + ) (f : EXP J [ ◇ A ]ᴶ) : Set ℓ where
       origin : ∀ {B}
                → (h : EXP A ⊢ B)
                → (f′ : ∀ {G} → EXP G ⊢ ◇ B → EXP J [ G ]ᴶ)
                → (pr : f ≡ f′ (m◇ h))
                → Origin J f

  mutual
    view : ∀ {B} ( J : Contextᴶ + ) (f : EXP J [ ◇ B ]ᴶ) → Origin J f
    view ([] <⊢ ._)       (m◇  f)   = origin f id refl

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
    view ((◇> A) <⊢ ._)   (m◇  f)   = go (A <⊢ _)               f m◇
    private
      go : ∀ {B}
         → ( I : Contextᴶ + ) (f : EXP I [ ◇ B ]ᴶ)
         → { J : Contextᴶ + } (g : ∀ {G} → EXP I [ G ]ᴶ → EXP J [ G ]ᴶ)
         → Origin J (g f)
      go I f {J} g with view I f
      ... | origin h f′ pr rewrite pr = origin h (g ∘ f′) refl
