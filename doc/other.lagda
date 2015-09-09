\begin{comment}
\begin{code}
module other where
\end{code}


\begin{code}
module Data_Bool_T where

  open import Data.Bool  using (Bool; true; false)
  open import Data.Empty using (⊥)
  open import Data.Unit  using (⊤)
\end{code}
%<*DataBoolT>
\begin{code}
  T : Bool → Set
  T true   = ⊤
  T false  = ⊥
\end{code}
%</DataBoolT>


\begin{code}
module Data_Traversable_traverse where

  open import Level                using (suc)
  open import Category.Applicative using (RawApplicative)

  record RawTraversable {t} (T : Set t → Set t) : Set (suc t) where
    field
\end{code}
%<*DataTraversabletraverse>
\begin{code}
      traverse : ∀ {F A B} {{AppF : RawApplicative F}} → (A → F B) → T A → F (T B)
\end{code}
%</DataTraversabletraverse>


\begin{code}
module OldTypeLogicalGrammar where

  record TypeLogicalGrammar : Set₁ where
    field
      Type            : Set
      Struct          : Set → Set
      _⊢_             : Struct Type → Type → Set
\end{code}
%<*OldTypeLogicalGrammar>
\begin{code}
    field
      ⟦_⟧ᵗ  : Type → Set
      ⟦_⟧   : ∀ {Γ B} → Γ ⊢ B → ⟦ B ⟧ᵗ
\end{code}
%</OldTypeLogicalGrammar>


\begin{code}
module SampleMeaningPostulates where

  open import Data.Bool using (Bool)
  data Entity : Set where
\end{code}
%<*SampleMeaningPostulates>
\begin{code}
  postulate
    FORALL     : (Entity → Bool) → Bool
    EXISTS     : (Entity → Bool) → Bool
    MARY       : Entity
    FIND       : Entity → Entity → Bool
    UNICORN    : Entity → Bool
    PERSON     : Entity → Bool
    LOVE       : Entity → Entity → Bool
\end{code}
%</SampleMeaningPostulates>


\begin{code}
module Polarity where
\end{code}
%<*Polarity>
\begin{code}
  data Polarity : Set where + - : Polarity
\end{code}
%</Polarity>


\end{comment}
