--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------


open import Function           using (id; flip)
open import Data.Bool          using (Bool; true; false; not; _∧_; _∨_)
open import Data.String        using (String)
open import Data.Product       using (Σ; Σ-syntax; _×_; proj₁; proj₂; _,_)
open import Data.List          using (_∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_; map)
open import Data.Traversable   using (module RawTraversable)
open import Data.Unit          using (⊤; tt)
open import Data.Vec           using (Vec)


module Example.System.AlgNL where


open import TypeLogicalGrammar
open import Example.System.Base public
open import Logic.Translation
open import Logic.Intuitionistic.Ordered.Lambek.ResMon             Atom          public
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.ProofSearch Atom _≟-Atom_ public
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.ToAgda      Atom ⟦_⟧ᵁ
open Translation NL→λΠ using (⟦_⟧ᵀ) renaming ([_] to [_]ᵀ)


np n s inf : Type
np   = el NP
n    = el N
s    = el S
inf  = el INF


private
  gq : (Entity → Bool) → ((Entity → _) → _) → (_ → _ → Bool) → List⁺ (Σ[ A ∈ Type ] ⟦ A ⟧ᵀ)
  gq p q _⊙_ = subj ∷ obj₁ ∷ obj₂ ∷ []
    where
      subj = (s ⇐ (np ⇒ s))
           , (λ v → q (λ x → p x ⊙ v x))
      obj₁ = (((np ⇒ s) ⇐ np) ⇒ (np ⇒ s))
           , (λ v x → q (λ y → p y ⊙ v y x))
      obj₂ = (((np ⇒ s) ⇐ np) ⇒ ((s ⇐ (np ⇒ s)) ⇒ s))
           , (λ v q′ → q (λ y → p y ⊙ q′ (λ x → v y x)))

  gq′ : ((Entity → Bool) → Bool) → (Bool → Bool → Bool) → List⁺ (Σ[ A ∈ Type ] ⟦ A ⟧ᵀ)
  gq′ q _⊙_ = subj ∷ obj₁ ∷ obj₂ ∷ []
    where
      subj = (s ⇐ (np ⇒ s)) ⇐ n
           , (λ v p → q (λ x → p x ⊙ v x))
      obj₁ = (((np ⇒ s) ⇐ np) ⇒ (np ⇒ s)) ⇐ n
           , (λ p v x → q (λ y → p y ⊙ v y x))
      obj₂ = (((np ⇒ s) ⇐ np) ⇒ ((s ⇐ (np ⇒ s)) ⇒ s)) ⇐ n
           , (λ p v q′ → q (λ y → p y ⊙ q′ (λ x → v y x)))

typeLogicalGrammar : TypeLogicalGrammar
typeLogicalGrammar = record
  { Type           = Type
  ; Struct         = Struct
  ; rawTraversable = rawTraversable
  ; _⊢_            = λ Γ B → NL ⌊ Γ ⌋ ⊢ B
  ; findAll        = λ Γ B → findAll (⌊ Γ ⌋ ⊢ B)
  ; s              = s
  ; toAgdaType     = ⟦_⟧ᵀ
  ; toAgdaTerm     = λ Γ f → [ f ]ᵀ (combine Γ)
  ; Word           = Word
  ; Lex            = Lex
  }
  where
    open RawTraversable rawTraversable using (_<$>_)

    ⌊_⌋ : Struct Type → Type
    ⌊ · A · ⌋ =       A
    ⌊ ⟨ X ⟩ ⌋ =     ⌊ X ⌋
    ⌊ X , Y ⌋ = ⌊ X ⌋ ⊗ ⌊ Y ⌋

    combine : (Γ : Struct (Σ Type ⟦_⟧ᵀ)) → ⟦ ⌊ proj₁ <$> Γ ⌋ ⟧ᵀ
    combine ·  A  · = proj₂ A
    combine ⟨  X  ⟩ = combine X
    combine (X , Y) = (combine X , combine Y)

    Lex : Word → List⁺ (Σ[ A ∈ Type ] ⟦ A ⟧ᵀ)
    Lex john     = (np , JOHN) ∷ []
    Lex mary     = (np , MARY) ∷ []
    Lex bill     = (np , BILL) ∷ []
    Lex unicorn  = (n , UNICORN) ∷ []
    Lex leave    = (inf , LEAVES) ∷ []
    Lex to       = ((np ⇒ s) ⇐ inf , id) ∷ []
    Lex left     = (np ⇒ s , LEAVES) ∷ []
    Lex smiles   = (np ⇒ s , SMILES) ∷ []
    Lex cheats   = (np ⇒ s , CHEATS) ∷ []
    Lex finds    = ((np ⇒ s) ⇐ np , (λ y x → x FINDS y)) ∷ []
    Lex loves    = ((np ⇒ s) ⇐ np , (λ y x → x LOVES y)) ∷ []
    Lex wants    = ((np ⇒ s) ⇐ s , (λ y x → x WANTS y)) ∷ []
    Lex said     = ((np ⇒ s) ⇐ s , (λ y x → x SAID y)) ∷ []
    Lex a        = gq′ EXISTS _∧_
    Lex some     = gq′ EXISTS _∧_
    Lex every    = gq′ FORALL _⊃_
    Lex everyone = gq PERSON FORALL _⊃_
    Lex someone  = gq PERSON EXISTS _∧_


open TypeLogicalGrammar.TypeLogicalGrammar typeLogicalGrammar public using (*_; ✓_; ⟦_⟧)
