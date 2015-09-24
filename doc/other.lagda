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
module Logic_NL_SC_Structure_Context (Atom : Set) where
  open import Logic.NL.SC.Structure         Atom using (Structure; _,_)
  open import Logic.NL.SC.Structure.Context Atom using (Context; []; _<,_; _,>_)
\end{code}
%<*Logic_NL_SC_Structure_Context>
\begin{code}
  _[_] : Context → Structure → Structure
  []         [ Δ ] = Δ
  (Γ ,> Γ′)  [ Δ ] = Γ , (Γ′ [ Δ ])
  (Γ <, Γ′)  [ Δ ] = (Γ [ Δ ]) , Γ′
\end{code}
%</Logic_NL_SC_Structure_Context>




\begin{code}
module Logic_NL_Context_J where
  open import Logic.Polarity
  open import Example.System.NL.ResMon using (Atom; Type)
  open import Logic.NL.Type.Context.Polarised Atom using (Context)
\end{code}
%<*Logic_NL_Context_J>
\begin{code}
  data Contextʲ (p : Polarity) : Set where
    _<⊢_  : Context p +  → Type         → Contextʲ p
    _⊢>_  : Type         → Context p -  → Contextʲ p
\end{code}
%</Logic_NL_Context_J>


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
module TraceContext where
  open import Data.Unit using (⊤)
  open import Logic.NLP.ResMon.Type ⊤ using (L; R)
  open import Logic.NLP.ResMon.Type.Context ⊤ using (Context; []; _⊗>_; _<⊗_)
\end{code}
%<*TraceContext>
\begin{code}
  TraceL : Context → Context
  TraceL []       = []
  TraceL (C ⊗> Γ) = C ⊗> (L ⊗> TraceL Γ)
  TraceL (Γ <⊗ C) = (L ⊗> TraceL Γ) <⊗ C

  TraceR : Context → Context
  TraceR []       = []
  TraceR (C ⊗> Γ) = C ⊗> (TraceR Γ <⊗ R)
  TraceR (Γ <⊗ C) = (TraceR Γ <⊗ R) <⊗ C
\end{code}
%</TraceContext>


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
