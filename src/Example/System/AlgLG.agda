------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function           using (id; flip)
open import Data.Bool          using (Bool; true; false; not; _∧_; _∨_)
open import Data.String        using (String)
open import Data.Product       using (Σ; Σ-syntax; _×_; proj₁; proj₂; _,_)
open import Data.List          using (_∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Traversable   using (module RawTraversable)
open import Data.Unit          using (⊤; tt)
open import Data.Vec           using (Vec)


module Example.System.AlgLG where


open import TypeLogicalGrammar
open import Example.System.Base public
open import Logic.Translation
open import Logic.Classical.Ordered.LambekGrishin.ResMon Atom public
open import Logic.Classical.Ordered.LambekGrishin.ResMon.ProofSearch Atom _≟-Atom_ public
open import Logic.Classical.Ordered.LambekGrishin.ResMon.ToAgda Atom Bool ⟦_⟧ᵁ using (CBV)
open Translation CBV using (⟦_⟧ᵀ) renaming ([_] to [_]ᵀ)



np n s inf : Type
np   = el NP
n    = el N
s    = el S
inf  = el INF


private
  im : (Entity → Bool) → ⟦ n ⇐ n ⟧ᵀ
  im f = λ {(k , g) → k (λ x → f x ∧ g x)}

  v₀ : (Entity → Bool) → ⟦ np ⇒ s ⟧ᵀ
  v₀ f = λ {(x , k) → k (f x)}

  v₁ : (Entity → Entity → Bool) → ⟦ (np ⇒ s) ⇐ np ⟧ᵀ
  v₁ f = λ {(k , y) → k (λ {(x , k) → k (f x y)})}

  gq  : (Entity → Bool) → ((Entity → Bool) → Bool) → (Bool → Bool → Bool) → ⟦ (np ⇐ n) ⊗ n ⟧ᵀ
  gq  f q _⊙_ = (λ {(g , f) → q (λ x → f x ⊙ g x)}) , f


typeLogicalGrammar : TypeLogicalGrammar
typeLogicalGrammar = record
  { Type           = Type
  ; Struct         = Struct
  ; rawTraversable = rawTraversable
  ; _⊢_            = λ Γ B → LG ⌊ Γ ⌋ ⊢ B
  ; findAll        = λ Γ B → findAll (⌊ Γ ⌋ ⊢ B)
  ; s              = s
  ; toAgdaType     = ⟦_⟧ᵀ
  ; toAgdaTerm     = λ Γ f → [ f ]ᵀ (combine Γ) id
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
    Lex to       = ((np ⇒ s) ⇐ inf , (λ {(k , p) → k (λ {(x , k) → k (p x)})})) ∷ []
    Lex left     = (np ⇒ s , v₀ LEAVES) ∷ []
    Lex smiles   = (np ⇒ s , v₀ SMILES) ∷ []
    Lex cheats   = (np ⇒ s , v₀ CHEATS) ∷ []
    Lex finds    = ((np ⇒ s) ⇐ np , v₁ _FINDS_) ∷ []
    Lex loves    = ((np ⇒ s) ⇐ np , v₁ _LOVES_) ∷ []
    Lex wants    = ((np ⇒ s) ⇐ s , (λ {(k , y) → k (λ {(x , k) → k (_WANTS_ x y)})})) ∷ []
    Lex said     = ((np ⇒ s) ⇐ s , (λ {(k , y) → k (λ {(x , k) → k (_SAID_  x y)})})) ∷ []
    Lex a        = ((np ⇐ n) , (λ {(n , v) → EXISTS (λ x → n x ∧ v x)})) ∷ []
    Lex some     = ((np ⇐ n) , (λ {(n , v) → EXISTS (λ x → n x ∧ v x)})) ∷ []
    Lex every    = ((np ⇐ n) , (λ {(n , v) → FORALL (λ x → n x ⊃ v x)})) ∷ []
    Lex everyone = ((np ⇐ n) ⊗ n , gq PERSON FORALL _⊃_) ∷ []
    Lex someone  = ((np ⇐ n) ⊗ n , gq PERSON EXISTS _∧_) ∷ []


open TypeLogicalGrammar.TypeLogicalGrammar typeLogicalGrammar public using (*_; ✓_; ⟦_⟧)
