------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements several views on proofs in the system ResMon which are
-- heavily used in the proof of admissibility of the transitivity rule.
--
-- One advantage of the residuation-monotonicity calculus is that
-- every connective *must* be introduced by an application of the
-- corresponding monotonicity-rule. The proofs in the `Origin` module
-- can be used to construct a view on a proof that makes this
-- introducing application of a monotonicity-rule explicit.
--
-- The proofs in this module are highly repetitive, and the decision
-- procedures and data structures could be abstracted over by
-- generalising over the connectives (cutting the file length by ±750
-- lines). However, I feel that abstracting over connectives would
-- make the logic a lot harder to read. I may do it in the future
-- anyway.
------------------------------------------------------------------------






open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong)






module Logic.LambekGrishin.ResMon.Origin {ℓ} (Univ : Set ℓ) where



open import Logic.Polarity
open import Logic.Type Univ
open import Logic.Judgement Type Type using (_⊢_)
open import Logic.Judgement.Context Univ as JC using ()
open import Logic.Type.Context.Polarised Univ
open import Logic.Judgement.Context.Polarised Univ renaming (Polarised to JudgementContext)
open import Logic.LambekGrishin.ResMon.Base Univ as LGB
open import Logic.LambekGrishin.ResMon.Derivation Univ as LGD












open JC.Simple using () renaming (_[_] to _[_]ᴶ)
open LGD.Simple using () renaming (_[_] to _[_]ᴰ; _<_> to _<_>ᴰ; <>-def to <>ᴰ-def)









module el where



  data Origin {J B} (J⁺ : JudgementContext + J) (f : LG J [ el B ]ᴶ) : Set ℓ where
       origin : (f′ : ∀ {G} → LG G ⊢ el B ⋯ J [ G ]ᴶ)
              → (pr : f ≡ f′ [ id ]ᴰ)
              → Origin J⁺ f



  mutual
    origin? : ∀ {J B} (J⁺ : JudgementContext + J) (f : LG J [ el B ]ᴶ) → Origin J⁺ f
    origin? ([] <⊢ ._)       id             = origin [] refl
    origin? ([] <⊢ ._)       (res-⊗⇒ f)     = go ((_ ⊗> []) <⊢ _)       f  (res-⊗⇒ [])
    origin? ([] <⊢ ._)       (res-⊗⇐ f)     = go (([] <⊗ _) <⊢ _)       f  (res-⊗⇐ [])
    origin? ((A ⊗> B) <⊢ ._) (mon-⊗  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⊗ᴿ f₁ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇒⊗ f)     = go (B <⊢ _)               f  (res-⇒⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (res-⇐⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])
    origin? ((A <⊗ B) <⊢ ._) (mon-⊗  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⊗ᴸ [] f₂)
    origin? ((A <⊗ B) <⊢ ._) (res-⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (res-⇒⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⇐⊗ f)     = go (A <⊢ _)               f  (res-⇐⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])
    origin? (._ ⊢> (A ⇒> B)) (mon-⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (mon-⇒ᴿ f₁ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⊗⇒ f)     = go (_ ⊢> B)               f  (res-⊗⇒ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (mon-⇐  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⇐ᴿ f₁ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (res-⊗⇐ [])
    origin? (._ ⊢> (A <⇒ B)) (mon-⇒  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⇒ᴸ [] f₂)
    origin? (._ ⊢> (A <⇒ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (res-⊗⇒ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (mon-⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (mon-⇐ᴸ [] f₂)
    origin? (._ ⊢> (A <⇐ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⊗⇐ f)     = go (_ ⊢> A)               f  (res-⊗⇐ [])



    private
      go : ∀ {I J B}
                     → (I⁺ : JudgementContext + I) (f : LG I [ el B ]ᴶ)
                     → {J⁺ : JudgementContext + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
                     → Origin J⁺ (g [ f ]ᴰ)
      go I⁺ f {J⁺} g with origin? I⁺ f
      ... | origin f′ pr = origin (g < f′ >ᴰ) pr′
        where
          pr′ : g [ f ]ᴰ ≡ (g < f′ >ᴰ) [ id ]ᴰ
          pr′ rewrite <>ᴰ-def g f′ id = cong (_[_]ᴰ g) pr















module ⊗ where



  data Origin {J B C} (J⁻ : JudgementContext - J) (f : LG J [ B ⊗ C ]ᴶ) : Set ℓ where
       origin : ∀ {E F}
                → (h₁ : LG E ⊢ B) (h₂ : LG F ⊢ C)
                → (f′ : ∀ {G} → LG E ⊗ F ⊢ G ⋯ J [ G ]ᴶ)
                → (pr : f ≡ f′ [ mon-⊗ h₁ h₂ ]ᴰ)
                → Origin J⁻ f



  mutual
    origin? : ∀ {J B C} (J⁻ : JudgementContext - J) (f : LG J [ B ⊗ C ]ᴶ) → Origin J⁻ f
    origin? (._ ⊢> [])       (mon-⊗  f₁ f₂) = origin f₁ f₂ [] refl
    origin? (._ ⊢> [])       (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> []))       f  (res-⇒⊗ [])
    origin? (._ ⊢> [])       (res-⇐⊗ f)     = go (_ ⊢> ([] <⇐ _))       f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇒> B)) (mon-⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (mon-⇒ᴿ f₁ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⊗⇒ f)     = go (_ ⊢> B)               f  (res-⊗⇒ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (mon-⇐  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⇐ᴿ f₁ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (res-⊗⇐ [])
    origin? (._ ⊢> (A <⇒ B)) (mon-⇒  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⇒ᴸ [] f₂)
    origin? (._ ⊢> (A <⇒ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (res-⊗⇒ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (mon-⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (mon-⇐ᴸ [] f₂)
    origin? (._ ⊢> (A <⇐ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⊗⇐ f)     = go (_ ⊢> A)               f  (res-⊗⇐ [])
    origin? ((A ⊗> B) <⊢ ._) (mon-⊗  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⊗ᴿ f₁ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇒⊗ f)     = go (B <⊢ _)               f  (res-⇒⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (res-⇐⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])
    origin? ((A <⊗ B) <⊢ ._) (mon-⊗  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⊗ᴸ [] f₂)
    origin? ((A <⊗ B) <⊢ ._) (res-⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (res-⇒⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⇐⊗ f)     = go (A <⊢ _)               f  (res-⇐⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])



    private
      go : ∀ {I J B C}
                     → (I⁻ : JudgementContext - I) (f : LG I [ B ⊗ C ]ᴶ)
                     → {J⁻ : JudgementContext - J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
                     → Origin J⁻ (g [ f ]ᴰ)
      go I⁻ f {J⁻} g with origin? I⁻ f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g < f′ >ᴰ) pr′
        where
          pr′ : g [ f ]ᴰ ≡ (g < f′ >ᴰ) [ mon-⊗ h₁ h₂ ]ᴰ
          pr′ rewrite <>ᴰ-def g f′ (mon-⊗ h₁ h₂) = cong (_[_]ᴰ g) pr


















       origin : ∀ {E F}
                → (h₁ : LG E ⊢ B) (h₂ : LG C ⊢ F)
                → Origin J⁻ f



  mutual
    origin? (._ ⊢> [])       (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> []))       f  (res-⇒⊗ [])
    origin? (._ ⊢> [])       (res-⇐⊗ f)     = go (_ ⊢> ([] <⇐ _))       f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇒> B)) (mon-⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (mon-⇒ᴿ f₁ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⊗⇒ f)     = go (_ ⊢> B)               f  (res-⊗⇒ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (mon-⇐  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⇐ᴿ f₁ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (res-⊗⇐ [])
    origin? (._ ⊢> (A <⇒ B)) (mon-⇒  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⇒ᴸ [] f₂)
    origin? (._ ⊢> (A <⇒ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (res-⊗⇒ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (mon-⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (mon-⇐ᴸ [] f₂)
    origin? (._ ⊢> (A <⇐ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⊗⇐ f)     = go (_ ⊢> A)               f  (res-⊗⇐ [])
    origin? ((A ⊗> B) <⊢ ._) (mon-⊗  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⊗ᴿ f₁ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇒⊗ f)     = go (B <⊢ _)               f  (res-⇒⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (res-⇐⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])
    origin? ((A <⊗ B) <⊢ ._) (mon-⊗  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⊗ᴸ [] f₂)
    origin? ((A <⊗ B) <⊢ ._) (res-⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (res-⇒⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⇐⊗ f)     = go (A <⊢ _)               f  (res-⇐⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])



    private
      go : ∀ {I J B C}
                     → {J⁻ : JudgementContext - J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
                     → Origin J⁻ (g [ f ]ᴰ)
      go I⁻ f {J⁻} g with origin? I⁻ f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g < f′ >ᴰ) pr′
        where


















       origin : ∀ {E F}
                → (h₁ : LG F ⊢ C) (h₂ : LG B ⊢ E)
                → Origin J⁻ f



  mutual
    origin? (._ ⊢> [])       (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> []))       f  (res-⇒⊗ [])
    origin? (._ ⊢> [])       (res-⇐⊗ f)     = go (_ ⊢> ([] <⇐ _))       f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇒> B)) (mon-⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (mon-⇒ᴿ f₁ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⊗⇒ f)     = go (_ ⊢> B)               f  (res-⊗⇒ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (mon-⇐  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⇐ᴿ f₁ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (res-⊗⇐ [])
    origin? (._ ⊢> (A <⇒ B)) (mon-⇒  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⇒ᴸ [] f₂)
    origin? (._ ⊢> (A <⇒ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (res-⊗⇒ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (mon-⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (mon-⇐ᴸ [] f₂)
    origin? (._ ⊢> (A <⇐ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⊗⇐ f)     = go (_ ⊢> A)               f  (res-⊗⇐ [])
    origin? ((A ⊗> B) <⊢ ._) (mon-⊗  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⊗ᴿ f₁ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇒⊗ f)     = go (B <⊢ _)               f  (res-⇒⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (res-⇐⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])
    origin? ((A <⊗ B) <⊢ ._) (mon-⊗  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⊗ᴸ [] f₂)
    origin? ((A <⊗ B) <⊢ ._) (res-⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (res-⇒⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⇐⊗ f)     = go (A <⊢ _)               f  (res-⇐⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])



    private
      go : ∀ {I J B C}
                     → {J⁻ : JudgementContext - J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
                     → Origin J⁻ (g [ f ]ᴰ)
      go I⁻ f {J⁻} g with origin? I⁻ f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g < f′ >ᴰ) pr′
        where















       origin : ∀ {E F}
                → (h₁ : LG B ⊢ E) (h₂ : LG C ⊢ F)
                → Origin J⁺ f



  mutual
    origin? ([] <⊢ ._)       (res-⊗⇒ f)     = go ((_ ⊗> []) <⊢ _)       f  (res-⊗⇒ [])
    origin? ([] <⊢ ._)       (res-⊗⇐ f)     = go (([] <⊗ _) <⊢ _)       f  (res-⊗⇐ [])
    origin? ((A ⊗> B) <⊢ ._) (mon-⊗  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⊗ᴿ f₁ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇒⊗ f)     = go (B <⊢ _)               f  (res-⇒⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (res-⇐⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])
    origin? ((A <⊗ B) <⊢ ._) (mon-⊗  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⊗ᴸ [] f₂)
    origin? ((A <⊗ B) <⊢ ._) (res-⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (res-⇒⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⇐⊗ f)     = go (A <⊢ _)               f  (res-⇐⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])
    origin? (._ ⊢> (A ⇒> B)) (mon-⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (mon-⇒ᴿ f₁ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⊗⇒ f)     = go (_ ⊢> B)               f  (res-⊗⇒ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (mon-⇐  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⇐ᴿ f₁ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (res-⊗⇐ [])
    origin? (._ ⊢> (A <⇒ B)) (mon-⇒  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⇒ᴸ [] f₂)
    origin? (._ ⊢> (A <⇒ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (res-⊗⇒ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (mon-⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (mon-⇐ᴸ [] f₂)
    origin? (._ ⊢> (A <⇐ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⊗⇐ f)     = go (_ ⊢> A)               f  (res-⊗⇐ [])



    private
      go : ∀ {I J B C}
                     → {J⁺ : JudgementContext + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
                     → Origin J⁺ (g [ f ]ᴰ)
      go I⁺ f {J⁺} g with origin? I⁺ f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g < f′ >ᴰ) pr′
        where












module ⇐ where



  data Origin {J B C} (J⁺ : JudgementContext + J) (f : LG J [ B ⇐ C ]ᴶ) : Set ℓ where
       origin : ∀ {E F}
                → (h₁ : LG B ⊢ E) (h₂ : LG F ⊢ C)
                → (f′ : ∀ {G} → LG G ⊢ E ⇐ F ⋯ J [ G ]ᴶ)
                → (pr : f ≡ f′ [ mon-⇐ h₁ h₂ ]ᴰ)
                → Origin J⁺ f



  mutual
    origin? : ∀ {J B C} (J⁺ : JudgementContext + J) (f : LG J [ B ⇐ C ]ᴶ) → Origin J⁺ f
    origin? ([] <⊢ ._)       (mon-⇐  f₁ f₂) = origin f₁ f₂ [] refl
    origin? ([] <⊢ ._)       (res-⊗⇒ f)     = go ((_ ⊗> []) <⊢ _)       f  (res-⊗⇒ [])
    origin? ([] <⊢ ._)       (res-⊗⇐ f)     = go (([] <⊗ _) <⊢ _)       f  (res-⊗⇐ [])
    origin? ((A ⊗> B) <⊢ ._) (mon-⊗  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⊗ᴿ f₁ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇒⊗ f)     = go (B <⊢ _)               f  (res-⇒⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (res-⇐⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])
    origin? ((A <⊗ B) <⊢ ._) (mon-⊗  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⊗ᴸ [] f₂)
    origin? ((A <⊗ B) <⊢ ._) (res-⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (res-⇒⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⇐⊗ f)     = go (A <⊢ _)               f  (res-⇐⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])
    origin? (._ ⊢> (A ⇒> B)) (mon-⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (mon-⇒ᴿ f₁ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⊗⇒ f)     = go (_ ⊢> B)               f  (res-⊗⇒ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (mon-⇐  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⇐ᴿ f₁ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (res-⊗⇐ [])
    origin? (._ ⊢> (A <⇒ B)) (mon-⇒  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⇒ᴸ [] f₂)
    origin? (._ ⊢> (A <⇒ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (res-⊗⇒ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (mon-⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (mon-⇐ᴸ [] f₂)
    origin? (._ ⊢> (A <⇐ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⊗⇐ f)     = go (_ ⊢> A)               f  (res-⊗⇐ [])



    private
      go : ∀ {I J B C}
                     → (I⁺ : JudgementContext + I) (f : LG I [ B ⇐ C ]ᴶ)
                     → {J⁺ : JudgementContext + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
                     → Origin J⁺ (g [ f ]ᴰ)
      go I⁺ f {J⁺} g with origin? I⁺ f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g < f′ >ᴰ) pr′
        where
          pr′ : g [ f ]ᴰ ≡ (g < f′ >ᴰ) [ mon-⇐ h₁ h₂ ]ᴰ
          pr′ rewrite <>ᴰ-def g f′ (mon-⇐ h₁ h₂) = cong (_[_]ᴰ g) pr












module ⇒ where



  data Origin {J B C} (J⁺ : JudgementContext + J) (f : LG J [ B ⇒ C ]ᴶ) : Set ℓ where
       origin : ∀ {E F}
                → (h₁ : LG E ⊢ B) (h₂ : LG C ⊢ F)
                → (f′ : ∀ {G} → LG G ⊢ E ⇒ F ⋯ J [ G ]ᴶ)
                → (pr : f ≡ f′ [ mon-⇒ h₁ h₂ ]ᴰ)
                → Origin J⁺ f



  mutual
    origin? : ∀ {J B C} (J⁺ : JudgementContext + J) (f : LG J [ B ⇒ C ]ᴶ) → Origin J⁺ f
    origin? ([] <⊢ ._)       (mon-⇒  f₁ f₂) = origin f₁ f₂ [] refl
    origin? ([] <⊢ ._)       (res-⊗⇒ f)     = go ((_ ⊗> []) <⊢ _)       f  (res-⊗⇒ [])
    origin? ([] <⊢ ._)       (res-⊗⇐ f)     = go (([] <⊗ _) <⊢ _)       f  (res-⊗⇐ [])
    origin? ((A ⊗> B) <⊢ ._) (mon-⊗  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⊗ᴿ f₁ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇒⊗ f)     = go (B <⊢ _)               f  (res-⇒⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (res-⇐⊗ [])
    origin? ((A ⊗> B) <⊢ ._) (res-⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])
    origin? ((A <⊗ B) <⊢ ._) (mon-⊗  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⊗ᴸ [] f₂)
    origin? ((A <⊗ B) <⊢ ._) (res-⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (res-⇒⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (res-⊗⇒ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⇐⊗ f)     = go (A <⊢ _)               f  (res-⇐⊗ [])
    origin? ((A <⊗ B) <⊢ ._) (res-⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (res-⊗⇐ [])
    origin? (._ ⊢> (A ⇒> B)) (mon-⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (mon-⇒ᴿ f₁ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⊗⇒ f)     = go (_ ⊢> B)               f  (res-⊗⇒ [])
    origin? (._ ⊢> (A ⇒> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (mon-⇐  f₁ f₂) = go (B <⊢ _)               f₂ (mon-⇐ᴿ f₁ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A ⇐> B)) (res-⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (res-⊗⇐ [])
    origin? (._ ⊢> (A <⇒ B)) (mon-⇒  f₁ f₂) = go (A <⊢ _)               f₁ (mon-⇒ᴸ [] f₂)
    origin? (._ ⊢> (A <⇒ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (res-⊗⇒ [])
    origin? (._ ⊢> (A <⇒ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (mon-⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (mon-⇐ᴸ [] f₂)
    origin? (._ ⊢> (A <⇐ B)) (res-⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (res-⇒⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (res-⇐⊗ [])
    origin? (._ ⊢> (A <⇐ B)) (res-⊗⇐ f)     = go (_ ⊢> A)               f  (res-⊗⇐ [])



    private
      go : ∀ {I J B C}
                     → (I⁺ : JudgementContext + I) (f : LG I [ B ⇒ C ]ᴶ)
                     → {J⁺ : JudgementContext + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
                     → Origin J⁺ (g [ f ]ᴰ)
      go I⁺ f {J⁺} g with origin? I⁺ f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g < f′ >ᴰ) pr′
        where
          pr′ : g [ f ]ᴰ ≡ (g < f′ >ᴰ) [ mon-⇒ h₁ h₂ ]ᴰ
          pr′ rewrite <>ᴰ-def g f′ (mon-⇒ h₁ h₂) = cong (_[_]ᴰ g) pr

