\documentclass[twocolumn]{article}

%include main.fmt
\include{preamble}

\begin{document}

\title{Symmetric Categorial Grammar in Agda}%
\author{Pepijn Kokke}%
\maketitle

\begin{abstract}
In recent years, the interest in using proof assistants to reason about
categorial grammars has grown.
\end{abstract}


\section{Introduction}


\section{Types, Judgements, Base System}

If we want to model our categorial grammars in Agda, a natural starting point
would be our atomic types---such as |n|, |np|, |s|, etc. These could easily be
represented as an enumerated data type. However, in order to avoid committing
to a certain set of atomic types, and side-step the debate on which types
\textit{should} be atomic, we will simply assume there is a some data type
representing our atomic types.
\begin{code}
module main (Univ : Set) where
\end{code}
Our types can easily be described as a data type, injecting our atomic types
by means of the constructor |el|, and adding the familiar connectives from the
Lambek Grishin calculus as binary constructors.\footnote{
  Agda uses underscores in definitions to denote the argument positions, so
  |_⊗_| defines an infix, binary connective.
} In the same manner, we will define a data type to represent judgements.
\begin{code}
data Type : Set ℓ where
  el           : Univ  → Type
  _⊗_ _⇒_ _⇐_  : Type  → Type  → Type
  _⊕_ _⇚_ _⇛_  : Type  → Type  → Type

data Judgement : Set ℓ where
  _⊢_  : Type → Type → Judgement
\end{code}
Using the above definitions, we can now write judgements such as |A ⊗ A ⇒ B ⊢ B|
as Agda values.
\hidden{
\begin{code}
infix   1   LG_
infixr  20  _⇒_
infixl  20  _⇐_
infixl  25  _⇚_
infixr  25  _⇛_
infixr  30  _⊗_
infixr  30  _⊕_
\end{code}}
\indent
Next we will define a data type to represent our logical system. This is where
our dependent type system gets a chance to shine! The constructors for our data
type will represent our axiomatic rules, and their types will be constrained by
judgements. Below you can see the entire system \textit{LG} as an Agda data
type.\footnote{
  For the typeset version of this paper we omit all implicit, universally
  quantified arguments, as is conventional in both Haskell~\citep{jones2003}
  and Idris~\citep{brady2013}, and in much of logic.
}
\begin{code}
data LG_ : Judgement → Set ℓ where

  ax   : ∀ {A}       →  LG el A ⊢ el A

  -- residuation and monotonicity for (⇐ , ⊗ , ⇒)
  r⇒⊗  : ∀ {A B C}   →  LG B ⊢ A ⇒ C  → LG A ⊗ B ⊢ C
  r⊗⇒  : ∀ {A B C}   →  LG A ⊗ B ⊢ C  → LG B ⊢ A ⇒ C
  r⇐⊗  : ∀ {A B C}   →  LG A ⊢ C ⇐ B  → LG A ⊗ B ⊢ C
  r⊗⇐  : ∀ {A B C}   →  LG A ⊗ B ⊢ C  → LG A ⊢ C ⇐ B

  m⊗   : ∀ {A B C D} →  LG A ⊢ B  → LG C ⊢ D  → LG A ⊗ C ⊢ B ⊗ D
  m⇒   : ∀ {A B C D} →  LG A ⊢ B  → LG C ⊢ D  → LG B ⇒ C ⊢ A ⇒ D
  m⇐   : ∀ {A B C D} →  LG A ⊢ B  → LG C ⊢ D  → LG A ⇐ D ⊢ B ⇐ C

  -- residuation and monotonicity for (⇚ , ⊕ , ⇛)
  r⇛⊕  : ∀ {A B C}   →  LG B ⇛ C ⊢ A  → LG C ⊢ B ⊕ A
  r⊕⇛  : ∀ {A B C}   →  LG C ⊢ B ⊕ A  → LG B ⇛ C ⊢ A
  r⊕⇚  : ∀ {A B C}   →  LG C ⊢ B ⊕ A  → LG C ⇚ A ⊢ B
  r⇚⊕  : ∀ {A B C}   →  LG C ⇚ A ⊢ B  → LG C ⊢ B ⊕ A

  m⊕   : ∀ {A B C D} →  LG A ⊢ B  → LG C ⊢ D  → LG A ⊕ C ⊢ B ⊕ D
  m⇛   : ∀ {A B C D} →  LG C ⊢ D  → LG A ⊢ B  → LG D ⇛ A ⊢ C ⇛ B
  m⇚   : ∀ {A B C D} →  LG A ⊢ B  → LG C ⊢ D  → LG A ⇚ D ⊢ B ⇚ C

  -- grishin distributives
  d⇛⇐  : ∀ {A B C D} →  LG A ⊗ B ⊢ C ⊕ D  → LG C ⇛ A ⊢ D ⇐ B
  d⇛⇒  : ∀ {A B C D} →  LG A ⊗ B ⊢ C ⊕ D  → LG C ⇛ B ⊢ A ⇒ D
  d⇚⇒  : ∀ {A B C D} →  LG A ⊗ B ⊢ C ⊕ D  → LG B ⇚ D ⊢ A ⇒ C
  d⇚⇐  : ∀ {A B C D} →  LG A ⊗ B ⊢ C ⊕ D  → LG A ⇚ D ⊢ C ⇐ B
\end{code}
Using this data type we can already do quite a lot. For instance, we can show
that while |ax| above is restricted to atomic types, the unrestricted version
is admissible, by induction on the type.
\begin{code}
ax′ : ∀ {A} → LG A ⊢ A
ax′ {A = el   _} = ax
ax′ {A = _ ⊗  _} = m⊗ ax′ ax′
ax′ {A = _ ⇐  _} = m⇐ ax′ ax′
ax′ {A = _ ⇒  _} = m⇒ ax′ ax′
ax′ {A = _ ⊕  _} = m⊕ ax′ ax′
ax′ {A = _ ⇚  _} = m⇚ ax′ ax′
ax′ {A = _ ⇛  _} = m⇛ ax′ ax′
\end{code}
Or we could derive the various (co-)applications that hold in the Lambek Grishin
calculus.
\begin{code}
appl-⇒′  : ∀ {A B} → LG A ⊗ (A ⇒ B) ⊢ B
appl-⇒′  = r⇒⊗ (m⇒ ax′ ax′)

appl-⇐′  : ∀ {A B} → LG (B ⇐ A) ⊗ A ⊢ B
appl-⇐′  = r⇐⊗ (m⇐ ax′ ax′)

appl-⇛′  : ∀ {A B} → LG B ⊢ A ⊕ (A ⇛ B)
appl-⇛′  = r⇛⊕ (m⇛ ax′ ax′)

appl-⇚′  : ∀ {A B} → LG B ⊢ (B ⇚ A) ⊕ A
appl-⇚′  = r⇚⊕ (m⇚ ax′ ax′)
\end{code}
But neither of those is really interesting compared to what is probably one of
the most compelling reasons to use this axiomatisation...


\section{Admissible Transitivity}

We would like to show that |trans′| of type |LG A ⊢ B → LG B ⊢ C → LG A ⊢ C| is
an admissible rule. The conventional proof for this reads as follows:
\begin{enumerate}[label= (\roman*)]
\item\label{p1} every connective is introduced \textit{symmetrically} by a
  monotonicity rule or axiom;
\item\label{p2} every connective has a side (antecedent or succedent) where,
  if it occurs there at the top level, it cannot be taken apart or moved by
  any inference rule;
\item\label{p3} due to~\ref{p1} and~\ref{p2}, when we find such an
  \textit{immovable} connective, we can be sure that after an arbitrary number
  of proof steps we will find the monotonicity rule which introduces that
  connective;
\item\label{p4} due to the type of |trans′|, when we match on the cut formula
  |B|, regardless of the main connective in |B|, we will always have a proof
  with an immovable variant of that connective;
\item\label{p5} finally, for each connective there exists a rewrite schema which
  makes use of the facts in~\ref{p3} and~\ref{p4} to rewrite an application of
  |trans′| to two smaller applications of |trans′| on the arguments of the
  connective (for binary connectives), or simply to a proof (in the case of
  atomic formulas). For example, the rewrite schema for |_⊗_| can be found
  in figure~\ref{cut:otimes}.
\end{enumerate}

\begin{figure*}[hb]%
  \footnotesize
  \hspace*{-\parindent}%
  \begin{minipage}{.47\linewidth}
    \begin{prooftree}
      \AXC{$E     \vdash B    $}
      \AXC{$    F \vdash     C$}
      \BIC{$E ⊗ F \vdash B ⊗ C$}
      \UIC{$      \vdots      $}
      \UIC{$A     \vdash B ⊗ C$}
      \AXC{$B ⊗ C \vdash D    $}
      \BIC{$A     \vdash D    $}
    \end{prooftree}
  \end{minipage}
  \begin{minipage}{.06\linewidth}
    $$\leadsto$$
  \end{minipage}
  \begin{minipage}{.47\linewidth}
    \begin{prooftree}
      \footnotesize
      \AXC{$E     \vdash B    $}
      \AXC{$    F \vdash C    $}
      \AXC{$B ⊗ C \vdash     D$}
      \UIC{$    C \vdash B \varbslash D$}
      \BIC{$    F \vdash B \varbslash D$}
      \UIC{$B ⊗ F \vdash     D$}
      \UIC{$B     \vdash D \varslash F$}
      \BIC{$E     \vdash D \varslash F$}
      \UIC{$E ⊗ F \vdash D    $}
      \UIC{$      \vdots      $}
      \UIC{$A     \vdash D    $}
    \end{prooftree}
  \end{minipage}%
\caption{Rewrite schema for cut on formula |B ⊗ C|.}
\label{cut:otimes}
\end{figure*}


\subsubsection*{Formula Contexts}

\begin{code}
data Context : Set ℓ where
  []              : Context
  _⊗>_ _⇒>_ _⇐>_  : Type     → Context  → Context
  _⊕>_ _⇚>_ _⇛>_  : Type     → Context  → Context
  _<⊗_ _<⇒_ _<⇐_  : Context  → Type     → Context
  _<⊕_ _<⇚_ _<⇛_  : Context  → Type     → Context
\end{code}

\begin{spec}
_[_]  : Context  → Type     → Type
_⟨_⟩  : Context  → Context  → Context
\end{spec}



\begin{spec}
data Polarised (p : Polarity) : Polarity → Context → Set ℓ where

  []    : Polarised p p []

  _⊗>_  : (A : Type) {B : Context}
        → Polarised p + B
        → Polarised p + (A ⊗> B)

  _⇒>_  : (A : Type) {B : Context}
        → Polarised p - B
        → Polarised p - (A ⇒> B)
  ...
\end{spec}


\subsubsection*{Origins}

\begin{spec}
  data Origin (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⊗ C ]ᴶ) : Set ℓ where
    origin :  (h₁  : LG E ⊢ B)
              (h₂  : LG F ⊢ C)
              (f′  : ∀ {G} → LG E ⊗ F ⊢ G ⋯ J [ G ]ᴶ)
              (pr  : f ≡ f′ $ m⊗ h₁ h₂)
                   → Origin J⁻ f
\end{spec}

\begin{spec}
  viewOrigin : (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⊗ C ]ᴶ) → Origin J⁻ f
  viewOrigin (._ ⊢> []) (m⊗  f g) = origin f g [] refl
  ...
\end{spec}

\begin{figure*}
\centering
\begin{spec}
trans′ : ∀ {A B C} (f : LG A ⊢ B) (g : LG B ⊢ C) → LG A ⊢ C
trans′ {B = el _ }  f  g with el.viewOrigin ([] <⊢ _) g
... | (el.origin        g′ pr)  = g′ f
trans′ {B = _ ⊗ _}  f  g with ⊗.viewOrigin (_ ⊢> []) f
... | (⊗.origin  h₁ h₂  f′ pr)  = f′ (r⇐⊗ (trans′ h₁ (r⊗⇐ (r⇒⊗ (trans′ h₂ (r⊗⇒ g))))))
trans′ {B = _ ⇐ _}  f  g with ⇐.viewOrigin ([] <⊢ _) g
... | (⇐.origin  h₁ h₂  g′ pr)  = g′ (r⊗⇐ (r⇒⊗ (trans′ h₂ (r⊗⇒ (trans′ (r⇐⊗ f) h₁)))))
trans′ {B = _ ⇒ _}  f  g with ⇒.viewOrigin ([] <⊢ _) g
... | (⇒.origin  h₁ h₂  g′ pr)  = g′ (r⊗⇒ (r⇐⊗ (trans′ h₁ (r⊗⇐ (trans′ (r⇒⊗ f) h₂)))))
trans′ {B = _ ⊕ _}  f  g with ⊕.viewOrigin ([] <⊢ _) g
... | (⊕.origin  h₁ h₂  g′ pr)  = g′ (r⇚⊕ (trans′ (r⊕⇚ (r⇛⊕ (trans′ (r⊕⇛ f) h₂))) h₁))
trans′ {B = _ ⇚ _}  f  g with ⇚.viewOrigin (_ ⊢> []) f
... | (⇚.origin  h₁ h₂  f′ pr)  = f′ (r⊕⇚ (r⇛⊕ (trans′ (r⊕⇛ (trans′ h₁ (r⇚⊕ g))) h₂)))
trans′ {B = _ ⇛ _}  f  g with ⇛.viewOrigin (_ ⊢> []) f
... | (⇛.origin  h₁ h₂  f′ pr)  = f′ (r⊕⇛ (r⇚⊕ (trans′ (r⊕⇚ (trans′ h₂ (r⇛⊕ g))) h₁)))
\end{spec}
\label{fun:trans}
\caption{Proof of admissible transitivity.}
\end{figure*}

\nocite{*}
\bibliographystyle{apalike}
\bibliography{main}

\end{document}
