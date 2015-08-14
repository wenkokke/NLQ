--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Origin/Sum.agda
--------------------------------------------------------------------------------


open import Function                              using (id; flip; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)


module Logic.MM96.ResMon.Origin.Plug {ℓ} (Atom : Set ℓ) where


  open import Logic.Polarity
  open import Logic.MM96.Type                               Atom as T
  open import Logic.MM96.Type.Context.Polarised             Atom as TC
  open import Logic.MM96.ResMon.Judgement                   Atom
  open import Logic.MM96.ResMon.Judgement.Context.Polarised Atom as JC
  open import Logic.MM96.ResMon.Base                        Atom as MM96B


  data Origin {B C} ( J : Contextᴶ + ) (f : MM96 J [ B ⊙ C ]ᴶ) : Set ℓ where
       origin : ∀ {E F}
                → (h₁ : MM96 B ⊢ E) (h₂ : MM96 C ⊢ F)
                → (f′ : ∀ {G} → MM96 G ⊢ E ⊙ F → MM96 J [ G ]ᴶ)
                → (pr : f ≡ f′ (m⊙ h₁ h₂))
                → Origin J f

  mutual
    view : ∀ {B C} ( J : Contextᴶ + ) (f : MM96 J [ B ⊙ C ]ᴶ) → Origin J f
    view ([] <⊢ ._)       (m⊙  f g) = origin f g id refl

    -- cases for (⇐ , ⊗ , ⇒) and (⇦ , ⊙ , ⇨)
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
    view ((A <⇦ _) <⊢ ._) (m⇦  f g) = go (A <⊢ _)               f (flip m⇦ g)
    view ((_ ⇦> B) <⊢ ._) (m⇦  f g) = go (_ ⊢> B)               g (m⇦ f)
    view ((A <⇨ _) <⊢ ._) (m⇨  f g) = go (_ ⊢> A)               f (flip m⇨ g)
    view ((_ ⇨> B) <⊢ ._) (m⇨  f g) = go (B <⊢ _)               g (m⇨ f)
    view (._ ⊢> (A <⊙ _)) (m⊙  f g) = go (_ ⊢> A)               f (flip m⊙ g)
    view (._ ⊢> (_ ⊙> B)) (m⊙  f g) = go (_ ⊢> B)               g (m⊙ f)
    view (A <⊢ ._)        (r⇦⊙ f)   = go ((A <⇦ _) <⊢ _)        f r⇦⊙
    view (._ ⊢> (_ ⊙> B)) (r⇦⊙ f)   = go ((_ ⇦> B) <⊢ _)        f r⇦⊙
    view (._ ⊢> (A <⊙ _)) (r⇦⊙ f)   = go (_ ⊢> A)               f r⇦⊙
    view ((A <⇦ _) <⊢ ._) (r⊙⇦ f)   = go (A <⊢ _)               f r⊙⇦
    view ((_ ⇦> B) <⊢ ._) (r⊙⇦ f)   = go (_ ⊢> (_ ⊙> B))        f r⊙⇦
    view (._ ⊢> B)        (r⊙⇦ f)   = go (_ ⊢> (B <⊙ _))        f r⊙⇦
    view (A <⊢ ._)        (r⇨⊙ f)   = go ((_ ⇨> A) <⊢ _)        f r⇨⊙
    view (._ ⊢> (_ ⊙> B)) (r⇨⊙ f)   = go (_ ⊢> B)               f r⇨⊙
    view (._ ⊢> (A <⊙ _)) (r⇨⊙ f)   = go ((A <⇨ _) <⊢ _)        f r⇨⊙
    view ((A <⇨ _) <⊢ ._) (r⊙⇨ f)   = go (_ ⊢> (A <⊙ _))        f r⊙⇨
    view ((_ ⇨> B) <⊢ ._) (r⊙⇨ f)   = go (B <⊢ _)               f r⊙⇨
    view (._ ⊢> B)        (r⊙⇨ f)   = go (_ ⊢> (_ ⊙> B))        f r⊙⇨
    view ((_ ⇨> B) <⊢ ._) (d⇨⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇨⇐
    view ((A <⇨ _) <⊢ ._) (d⇨⇐ f)   = go (_ ⊢> (A <⊙ _))        f d⇨⇐
    view (._ ⊢> (A <⇐ _)) (d⇨⇐ f)   = go (_ ⊢> (_ ⊙> A))        f d⇨⇐
    view (._ ⊢> (_ ⇐> B)) (d⇨⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇨⇐
    view ((_ ⇨> B) <⊢ ._) (d⇨⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇨⇒
    view ((A <⇨ _) <⊢ ._) (d⇨⇒ f)   = go (_ ⊢> (A <⊙ _))        f d⇨⇒
    view (._ ⊢> (_ ⇒> B)) (d⇨⇒ f)   = go (_ ⊢> (_ ⊙> B))        f d⇨⇒
    view (._ ⊢> (A <⇒ _)) (d⇨⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇨⇒
    view ((_ ⇦> B) <⊢ ._) (d⇦⇒ f)   = go (_ ⊢> (_ ⊙> B))        f d⇦⇒
    view ((A <⇦ _) <⊢ ._) (d⇦⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇦⇒
    view (._ ⊢> (_ ⇒> B)) (d⇦⇒ f)   = go (_ ⊢> (B <⊙ _))        f d⇦⇒
    view (._ ⊢> (A <⇒ _)) (d⇦⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇦⇒
    view ((_ ⇦> B) <⊢ ._) (d⇦⇐ f)   = go (_ ⊢> (_ ⊙> B))        f d⇦⇐
    view ((A <⇦ _) <⊢ ._) (d⇦⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇦⇐
    view (._ ⊢> (_ ⇐> B)) (d⇦⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇦⇐
    view (._ ⊢> (A <⇐ _)) (d⇦⇐ f)   = go (_ ⊢> (A <⊙ _))        f d⇦⇐

    -- cases for (⟨l⟩ , ⟨r⟩)
    view (._ ⊢> (⟨l⟩> B))   (m⟨l⟩  f)   = go (_ ⊢> B)               f m⟨l⟩
    view ((⟨r⟩> A) <⊢ ._)   (m⟨r⟩  f)   = go (A <⊢ _)               f m⟨r⟩
    view (._ ⊢> B)        (r⟨l⟩⟨r⟩ f)   = go (_ ⊢> (⟨l⟩> B))          f r⟨l⟩⟨r⟩
    view ((⟨r⟩> A) <⊢ ._)   (r⟨l⟩⟨r⟩ f)   = go (A <⊢ _)               f r⟨l⟩⟨r⟩
    view (A <⊢ ._)        (r⟨r⟩⟨l⟩ f)   = go ((⟨r⟩> A) <⊢ _)          f r⟨r⟩⟨l⟩
    view (._ ⊢> (⟨l⟩> B))   (r⟨r⟩⟨l⟩ f)   = go (_ ⊢> B)               f r⟨r⟩⟨l⟩

    private
      go : ∀ {B C}
         → ( I : Contextᴶ + ) (f : MM96 I [ B ⊙ C ]ᴶ)
         → { J : Contextᴶ + } (g : ∀ {G} → MM96 I [ G ]ᴶ → MM96 J [ G ]ᴶ)
         → Origin J (g f)
      go I f {J} g with view I f
      ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl
