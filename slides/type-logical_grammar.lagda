\documentclass[12pt,t,handout]{beamer}
\setbeameroption{show notes}

%include agda.fmt
%if False
\include{agda}
%endif
\include{common}

\title{Type-logical grammar in Agda}
\author[Kokke]{Pepijn Kokke}
\institute[UU]{Utrecht University}
\date{August 6th 2015}
\begin{document}

\begin{comment}
\begin{code}
{-# OPTIONS --type-in-type #-}
open import Level                                      using (zero)
open import Function                                   using (id; flip; _∘_)
open import Category.Monad                             using (module RawMonad; module RawMonadPlus; RawMonadPlus)
open import Category.Applicative                       using (module RawApplicative; RawApplicative)
open import Data.Bool                                  using (not; T)
open import Data.Maybe                                 using (Maybe; From-just; from-just)
open import Data.List                                  using (List; _∷_; []; _++_; map; null)
open import Data.List.Any                              using (any)
open import Data.List.NonEmpty                         using (List⁺; _∷_; foldr₁) renaming (map to map⁺)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Data.Sum                                   using (_⊎_; inj₁; inj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (IsPreorder)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong; cong₂; subst)

module type-logical_grammar where

private
  instance
    rawApplicative = RawMonad.rawIApplicative (Data.List.NonEmpty.monad {f = zero})
\end{code}
\end{comment}

\begin{frame}
  \maketitle
\end{frame}

\begin{comment}
\begin{code}
module non-associative_lambek_calculus (Atom : Set) (_≟-Atom_ : (x y : Atom) → Dec (x ≡ y))where
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  infix  1 NL_
  infix  2 _[_]ᴶ
  infix  3 _⊢_ _⊢>_ _<⊢_
  infixl 4 _[_]
  infixr 5 _⇒_ _⇒>_ _<⇒_
  infixl 5 _⇐_ _⇐>_ _<⇐_
  infixr 6 _⊗_ _⊗>_ _<⊗_
\end{code}
\end{comment}

\begin{frame}{Take-home message}
\centering\vfill
Machine-checked linguistic theories, which are directly embedded in a
published work, are within reach.
\vfill
{\tiny (Sometimes a little bit of typesetting is nice, though.)}
\note{%
I've always heard it's a good idea to start with your take-home
message, before all your listeners doze off due to all the details
you're discussing. So here it is:
}
\end{frame}

\begin{frame}{Example}
\centering\vfill
\only<1>{%
\ExecuteMetaData{example}
}
\only<2>{%
\ExecuteMetaData{preorder}
}
\vfill
\only<1>{%
{\tiny (The constructors of the parse tree have been omitted, as they are superfluous.)}
}
\only<2>{%
{\tiny (I realise this doesn't say much at the moment, but we're getting there.)}
}
\note{}
\end{frame}

\begin{frame}{Types and judgement}
\centering\vfill
\begin{code}
  data Type : Set where
    el   : Atom  → Type
    _⊗_  : Type  → Type → Type
    _⇒_  : Type  → Type → Type
    _⇐_  : Type  → Type → Type

  data Judgement : Set where
    _⊢_ : Type → Type → Judgement
\end{code}
\vfill
\note{}
\end{frame}

\begin{frame}{The non-associative Lambek calculus}
\centering\vfill
\begin{code}
  data NL_ : Judgement → Set where

    ax   : ∀ {A} → NL el A ⊢ el A

    m⊗   : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⊗ C ⊢ B ⊗ D
    m⇒   : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL B ⇒ C ⊢ A ⇒ D
    m⇐   : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⇐ D ⊢ B ⇐ C

    r⇒⊗  : ∀ {A B C} → NL B ⊢ A ⇒ C → NL A ⊗ B ⊢ C
    r⊗⇒  : ∀ {A B C} → NL A ⊗ B ⊢ C → NL B ⊢ A ⇒ C
    r⇐⊗  : ∀ {A B C} → NL A ⊢ C ⇐ B → NL A ⊗ B ⊢ C
    r⊗⇐  : ∀ {A B C} → NL A ⊗ B ⊢ C → NL A ⊢ C ⇐ B
\end{code}
\vfill
{\tiny (Each judgement should be prefixed with \AgdaDatatype{NL}.
        We are omitting this for readability.)}
\note{}
\end{frame}


\begin{frame}{Identity expansion}
\centering\vfill
\begin{code}
  ax′ : ∀ {A} → NL A ⊢ A
  ax′ {A =  el   A} = ax
  ax′ {A =  A ⊗  B} = m⊗  ax′ ax′
  ax′ {A =  A ⇐  B} = m⇐  ax′ ax′
  ax′ {A =  A ⇒  B} = m⇒  ax′ ax′
\end{code}
\vfill
{\tiny ($\AgdaSymbol{\{}\AgdaArgument{A} \AgdaSymbol{=} \AgdaBound{...}\AgdaSymbol{\}}$ is Agda syntax to match on implicit parameters.)}
\note{}
\end{frame}

\begin{frame}{Cut elimination}
\vfill
\begin{itemize}
\item
  Only monotonicity rules introduce connectives.

\item
  Residuation rules affect each connective on one side only.

\item
  In a cut, we have the main connective on both sides, so we can
  always find the monotonicity rule which introduced it.

\item
  We then replace it with two smaller cuts, glued together with
  residuation rules.
\end{itemize}
\vfill
\note{}
\end{frame}

\begin{comment}
\begin{code}
  module ⊗′ where
\end{code}
\end{comment}

\begin{frame}{Origins}
\only<1>{%
For instance, in the case of \AgdaInductiveConstructor{⊗}:\\
}
\vfill
\only<1>{%
\noindent
\begin{minipage}{.45\linewidth}
\begin{prooftree}
\footnotesize%
\AXC{$E     \vdash B    $}
\AXC{$    F \vdash     C$}
\BIC{$E ⊗ F \vdash B ⊗ C$}
\UIC{$      \vdots      $}
\UIC{$A     \vdash B ⊗ C$}
\AXC{$B ⊗ C \vdash D    $}
\BIC{$A     \vdash D    $}
\end{prooftree}
\end{minipage}
\begin{minipage}{.03\linewidth}
\footnotesize$$\leadsto$$
\end{minipage}
\begin{minipage}{.45\linewidth}
\begin{prooftree}
\footnotesize%
\AXC{$E           \vdash B             $}
\AXC{$          F \vdash C             $}
\AXC{$B \otimes C \vdash              D$}
\UIC{$          C \vdash B \varbslash D$}
\BIC{$          F \vdash B \varbslash D$}
\UIC{$B \otimes F \vdash              D$}
\UIC{$B           \vdash D \varbslash F$}
\BIC{$E           \vdash D \varbslash F$}
\UIC{$E \otimes F \vdash D             $}
\UIC{$            \vdots               $}
\UIC{$A           \vdash D             $}
\end{prooftree}
\end{minipage}
}
\only<2>{%
\begin{prooftree}
\AXC{$E           \vdash B          $}
\AXC{$          F \vdash           C$}
\BIC{$E \otimes F \vdash B \otimes C$}
\UIC{$            \vdots            $}
\UIC{$A           \vdash B \otimes C$}
\end{prooftree}
}
\only<3>{%
\begin{prooftree}
\AXC{\AgdaBound{$h_1$} \AgdaSymbol{:} $ E \vdash B$}
\AXC{\AgdaBound{$h_2$} \AgdaSymbol{:} $ F \vdash C$}
\BIC{\AgdaInductiveConstructor{m⊗} \AgdaBound{$h_1$} \AgdaBound{$h_2$} \AgdaSymbol{:} $E \otimes F \vdash B \otimes C$}
\UIC{\AgdaBound{f′} \AgdaSymbol{:} $\vdots$}
\UIC{\AgdaBound{f′} \AgdaSymbol{(}\AgdaInductiveConstructor{m⊗} \AgdaBound{$h_1$} \AgdaBound{$h_2$}\AgdaSymbol{)} \AgdaSymbol{:} $A \vdash B \otimes C$}
\end{prooftree}
}
\only<4>{%
\noindent
\begin{code}
    data  Origin′ {A B C}
          ( f : NL A ⊢ B ⊗ C )
          : Set where

          origin  : ∀ {E F} →  (h₁  : NL E ⊢ B)
                  →            (h₂  : NL F ⊢ C)
                  →            (f′  : NL E ⊗ F ⊢ B ⊗ C → NL A ⊢ B ⊗ C)
                  →            (pr  : f ≡ f′ (m⊗ h₁ h₂))
                  →            Origin′ f
\end{code}
}
\only<5>{%
\begin{prooftree}
\AXC{$               E           \vdash B                       $}
\AXC{$                         F \vdash           C             $}
\BIC{$               E \otimes F \vdash B \otimes C             $}
\UIC{$                           \vdots                         $}
\UIC{$               A \otimes D \vdash B \otimes C             $}
\end{prooftree}
}
\only<6>{%
\begin{prooftree}
\AXC{$               E           \vdash  B                        $}
\AXC{$                         F \vdash            C              $}
\BIC{$               E \otimes F \vdash  B \otimes C              $}
\UIC{$                           \vdots                           $}
\UIC{$ \color{green} A           \vdash (B \otimes C) \varslash D $}
\UIC{$               A \otimes D \vdash  B \otimes C              $}
\end{prooftree}
}
\vfill
\note{}
\end{frame}

\begin{frame}{Contexts}
\centering\vfill
\only<1>{%
\begin{code}
  data Polarity : Set where + - : Polarity

  data Context (p : Polarity) : Polarity → Set where
    []    : Context p p
    _⊗>_  : Type         → Context p +  → Context p +
    _⇒>_  : Type         → Context p -  → Context p -
    _⇐>_  : Type         → Context p +  → Context p -
    _<⊗_  : Context p +  → Type         → Context p +
    _<⇒_  : Context p +  → Type         → Context p -
    _<⇐_  : Context p -  → Type         → Context p -
\end{code}
}
\only<2>{%
\begin{code}
  _[_] : ∀ {p₁ p₂} → Context p₁ p₂ → Type → Type
  []      [ A ] = A
  B ⊗> C  [ A ] = B ⊗ (C [ A ])
  B ⇒> C  [ A ] = B ⇒ (C [ A ])
  B ⇐> C  [ A ] = B ⇐ (C [ A ])
  C <⊗ B  [ A ] = (C [ A ]) ⊗ B
  C <⇒ B  [ A ] = (C [ A ]) ⇒ B
  C <⇐ B  [ A ] = (C [ A ]) ⇐ B
\end{code}
}
\only<3>{%
\begin{code}
  data Contextᴶ (p : Polarity) : Set where
    _<⊢_  : Context p +  → Type         → Contextᴶ p
    _⊢>_  : Type         → Context p -  → Contextᴶ p

  _[_]ᴶ : ∀ {p} → Contextᴶ p → Type → Judgement
  A <⊢ B [ C ]ᴶ = A [ C ] ⊢ B
  A ⊢> B [ C ]ᴶ = A ⊢ B [ C ]
\end{code}
}
\vfill
\only<1>{%
So now we can write, e.g. \AgdaInductiveConstructor{[]} %
\AgdaInductiveConstructor{<$\varslash$} \AgdaSymbol{\_}
}
\note{}
\end{frame}


\begin{comment}
\begin{code}
  module ⊗ where
\end{code}
\end{comment}

\begin{frame}{Origins (revisited)}
\centering\vfill
\begin{code}
    data  Origin {B C}
          ( J : Contextᴶ - )
          ( f : NL J [ B ⊗ C ]ᴶ )
          : Set where

          origin  : ∀ {E F} →  (h₁  : NL E ⊢ B)
                  →            (h₂  : NL F ⊢ C)
                  →            (f′  : ∀ {G} → NL E ⊗ F ⊢ G → NL J [ G ]ᴶ)
                  →            (pr  : f ≡ f′ (m⊗ h₁ h₂))
                  →            Origin J f
\end{code}
\vfill
{\tiny (Function \AgdaBound{f′} should work for \textit{any} type \AgdaBound{G}.)}
\note{}
\end{frame}

\begin{comment}
\begin{code}
    mutual
\end{code}
\end{comment}

\begin{frame}{Origins (revisited)}
\centering\vfill
\begin{varwidth}{\linewidth}
\begin{code}
      view : ∀ {B C} ( J : Contextᴶ - ) (f : NL J [ B ⊗ C ]ᴶ) → Origin J f
      view (._ ⊢> []) (m⊗ f g)  =  origin f g id refl
      view (._ ⊢> []) (r⇒⊗ f)   =  wrap { _ ⊢> (_ ⇒> []) } r⇒⊗ f
      view (._ ⊢> []) (r⇐⊗ f)   =  wrap { _ ⊢> ([] <⇐ _) } r⇐⊗ f
\end{code}
\centering\vdots
\vspace{2ex}
\vfill
\onslide<2>{
\ExecuteMetaData{wrap}
}
\end{varwidth}
\vfill
\onslide<2>{
{\tiny (A \AgdaKeyword{with} statement is a way to pattern match on the result of a function.)}
}
\note{}
\end{frame}

\begin{comment}
\begin{code}
      view ((_ ⊗> A) <⊢ ._)  (m⊗   f g)  =  wrap {A <⊢ _              }  (      m⊗ f)  g
      view ((_ ⊗> A) <⊢ ._)  (r⇒⊗  f)    =  wrap {A <⊢ _              }         r⇒⊗    f
      view ((_ ⊗> A) <⊢ ._)  (r⊗⇒  f)    =  wrap {(_ ⊗> (_ ⊗> A)) <⊢ _}         r⊗⇒    f
      view ((_ ⊗> A) <⊢ ._)  (r⇐⊗  f)    =  wrap {_ ⊢> (_ ⇐> A)       }         r⇐⊗    f
      view ((_ ⊗> A) <⊢ ._)  (r⊗⇐  f)    =  wrap {((_ ⊗> A) <⊗ _) <⊢ _}         r⊗⇐    f
      view ((A <⊗ _) <⊢ ._)  (m⊗   f g)  =  wrap {A <⊢ _              }  (flip  m⊗ g)  f
      view ((A <⊗ _) <⊢ ._)  (r⇒⊗  f)    =  wrap {_ ⊢> (A <⇒ _)       }         r⇒⊗    f
      view ((A <⊗ _) <⊢ ._)  (r⊗⇒  f)    =  wrap {(_ ⊗> (A <⊗ _)) <⊢ _}         r⊗⇒    f
      view ((A <⊗ _) <⊢ ._)  (r⇐⊗  f)    =  wrap {A <⊢ _              }         r⇐⊗    f
      view ((A <⊗ _) <⊢ ._)  (r⊗⇐  f)    =  wrap {((A <⊗ _) <⊗ _) <⊢ _}         r⊗⇐    f
      view (._ ⊢> (_ ⇒> A))  (m⇒   f g)  =  wrap {_ ⊢> A              }  (      m⇒ f)  g
      view (._ ⊢> (_ ⇒> A))  (r⇒⊗  f)    =  wrap {_ ⊢> (_ ⇒> (_ ⇒> A))}         r⇒⊗    f
      view (._ ⊢> (_ ⇒> A))  (r⊗⇒  f)    =  wrap {_ ⊢> A              }         r⊗⇒    f
      view (._ ⊢> (_ ⇒> A))  (r⇐⊗  f)    =  wrap {_ ⊢> ((_ ⇒> A) <⇐ _)}         r⇐⊗    f
      view (._ ⊢> (_ ⇐> A))  (m⇐   f g)  =  wrap {A <⊢ _              }  (      m⇐ f)  g
      view (._ ⊢> (_ ⇐> A))  (r⇒⊗  f)    =  wrap {_ ⊢> (_ ⇒> (_ ⇐> A))}         r⇒⊗    f
      view (._ ⊢> (_ ⇐> A))  (r⇐⊗  f)    =  wrap {_ ⊢> ((_ ⇐> A) <⇐ _)}         r⇐⊗    f
      view (._ ⊢> (_ ⇐> A))  (r⊗⇐  f)    =  wrap {(_ ⊗> A) <⊢ _       }         r⊗⇐    f
      view (._ ⊢> (A <⇒ _))  (m⇒   f g)  =  wrap {A <⊢ _              }  (flip  m⇒ g)  f
      view (._ ⊢> (A <⇒ _))  (r⇒⊗  f)    =  wrap {_ ⊢> (_ ⇒> (A <⇒ _))}         r⇒⊗    f
      view (._ ⊢> (A <⇒ _))  (r⊗⇒  f)    =  wrap {(A <⊗ _) <⊢ _       }         r⊗⇒    f
      view (._ ⊢> (A <⇒ _))  (r⇐⊗  f)    =  wrap {_ ⊢> ((A <⇒ _) <⇐ _)}         r⇐⊗    f
      view (._ ⊢> (A <⇐ _))  (m⇐   f g)  =  wrap {_ ⊢> A              }  (flip  m⇐ g)  f
      view (._ ⊢> (A <⇐ _))  (r⇒⊗  f)    =  wrap {_ ⊢> (_ ⇒> (A <⇐ _))}         r⇒⊗    f
      view (._ ⊢> (A <⇐ _))  (r⇐⊗  f)    =  wrap {_ ⊢> ((A <⇐ _) <⇐ _)}         r⇐⊗    f
      view (._ ⊢> (A <⇐ _))  (r⊗⇐  f)    =  wrap {_ ⊢> A              }         r⊗⇐    f
\end{code}
\end{comment}

\begin{comment}
%<*wrap>
\begin{code}
      wrap : ∀ { I : Contextᴶ - } { J : Contextᴶ - } {B C} (g : ∀ {G} → NL I [ G ]ᴶ → NL J [ G ]ᴶ) (f : NL I [ B ⊗ C ]ᴶ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g ∘ f′) (cong g pr)
\end{code}
%</wrap>
\end{comment}

\begin{comment}
\begin{code}
  module el where

    data Origin {B} ( J : Contextᴶ + ) (f : NL J [ el B ]ᴶ) : Set where
         origin  : (f′ : ∀ {G} → NL G ⊢ el B → NL J [ G ]ᴶ)
                 → (pr : f ≡ f′ ax)
                 → Origin J f

    mutual
      view : ∀ {B} ( J : Contextᴶ + ) (f : NL J [ el B ]ᴶ) → Origin J f
      view ([] <⊢ ._)        ax         = origin id refl
      view ([] <⊢ ._)        (r⊗⇒ f)    = wrap {(_ ⊗> []) <⊢ _}               r⊗⇒   f
      view ([] <⊢ ._)        (r⊗⇐ f)    = wrap {([] <⊗ _) <⊢ _}               r⊗⇐   f
      view ((A ⊗> B) <⊢ ._)  (m⊗  f g)  = wrap {B <⊢ _}                (      m⊗ f) g
      view ((A ⊗> B) <⊢ ._)  (r⇒⊗ f)    = wrap {B <⊢ _}                       r⇒⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A ⊗> B)) <⊢ _}         r⊗⇒   f
      view ((A ⊗> B) <⊢ ._)  (r⇐⊗ f)    = wrap {_ ⊢> (_ ⇐> B)}                r⇐⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A ⊗> B) <⊗ _) <⊢ _}         r⊗⇐   f
      view ((A <⊗ B) <⊢ ._)  (m⊗  f g)  = wrap {A <⊢ _}                (flip  m⊗ g) f
      view ((A <⊗ B) <⊢ ._)  (r⇒⊗ f)    = wrap {_ ⊢> (A <⇒ _)}                r⇒⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A <⊗ B)) <⊢ _}         r⊗⇒   f
      view ((A <⊗ B) <⊢ ._)  (r⇐⊗ f)    = wrap {A <⊢ _}                       r⇐⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A <⊗ B) <⊗ _) <⊢ _}         r⊗⇐   f
      view (._ ⊢> (A ⇒> B))  (m⇒  f g)  = wrap {_ ⊢> B}                (      m⇒ f) g
      view (._ ⊢> (A ⇒> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇒> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇒> B))  (r⊗⇒ f)    = wrap {_ ⊢> B}                       r⊗⇒   f
      view (._ ⊢> (A ⇒> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇒> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (m⇐  f g)  = wrap {B <⊢ _}                (      m⇐ f) g
      view (._ ⊢> (A ⇐> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇐> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇐> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇐> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (r⊗⇐ f)    = wrap {(_ ⊗> B) <⊢ _}                r⊗⇐   f
      view (._ ⊢> (A <⇒ B))  (m⇒  f g)  = wrap {A <⊢ _}                (flip  m⇒ g) f
      view (._ ⊢> (A <⇒ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇒ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇒ B))  (r⊗⇒ f)    = wrap {(A <⊗ _) <⊢ _}                r⊗⇒   f
      view (._ ⊢> (A <⇒ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇒ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (m⇐  f g)  = wrap {_ ⊢> A}                (flip  m⇐ g) f
      view (._ ⊢> (A <⇐ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇐ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇐ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇐ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (r⊗⇐ f)    = wrap {_ ⊢> A}                       r⊗⇐   f

      wrap : ∀ { I : Contextᴶ + } { J : Contextᴶ + } {B}
           →   (g : ∀ {G} → NL I [ G ]ᴶ → NL J [ G ]ᴶ) (f : NL I [ el B ]ᴶ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin f′ pr = origin (g ∘ f′) (cong g pr)

  module ⇒ where

    data Origin {B C} ( J : Contextᴶ + ) (f : NL J [ B ⇒ C ]ᴶ) : Set where
         origin  : ∀ {E F}
                 →  (h₁  : NL E ⊢ B)
                 →  (h₂  : NL C ⊢ F)
                 →  (f′  : ∀ {G} → NL G ⊢ E ⇒ F → NL J [ G ]ᴶ)
                 →  (pr  : f ≡ f′ (m⇒ h₁ h₂))
                 →  Origin J f

    mutual
      view : ∀ {B C} ( J : Contextᴶ + ) (f : NL J [ B ⇒ C ]ᴶ) → Origin J f
      view ([] <⊢ ._)        (m⇒  f g)  = origin f g id refl
      view ([] <⊢ ._)        (r⊗⇒ f)    = wrap {(_ ⊗> []) <⊢ _}               r⊗⇒   f
      view ([] <⊢ ._)        (r⊗⇐ f)    = wrap {([] <⊗ _) <⊢ _}               r⊗⇐   f
      view ((A ⊗> B) <⊢ ._)  (m⊗  f g)  = wrap {B <⊢ _}                (      m⊗ f) g
      view ((A ⊗> B) <⊢ ._)  (r⇒⊗ f)    = wrap {B <⊢ _}                       r⇒⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A ⊗> B)) <⊢ _}         r⊗⇒   f
      view ((A ⊗> B) <⊢ ._)  (r⇐⊗ f)    = wrap {_ ⊢> (_ ⇐> B)}                r⇐⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A ⊗> B) <⊗ _) <⊢ _}         r⊗⇐   f
      view ((A <⊗ B) <⊢ ._)  (m⊗  f g)  = wrap {A <⊢ _}                (flip  m⊗ g) f
      view ((A <⊗ B) <⊢ ._)  (r⇒⊗ f)    = wrap {_ ⊢> (A <⇒ _)}                r⇒⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A <⊗ B)) <⊢ _}         r⊗⇒   f
      view ((A <⊗ B) <⊢ ._)  (r⇐⊗ f)    = wrap {A <⊢ _}                       r⇐⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A <⊗ B) <⊗ _) <⊢ _}         r⊗⇐   f
      view (._ ⊢> (A ⇒> B))  (m⇒  f g)  = wrap {_ ⊢> B}                (      m⇒ f) g
      view (._ ⊢> (A ⇒> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇒> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇒> B))  (r⊗⇒ f)    = wrap {_ ⊢> B}                       r⊗⇒   f
      view (._ ⊢> (A ⇒> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇒> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (m⇐  f g)  = wrap {B <⊢ _}                (      m⇐ f) g
      view (._ ⊢> (A ⇐> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇐> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇐> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇐> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (r⊗⇐ f)    = wrap {(_ ⊗> B) <⊢ _}                r⊗⇐   f
      view (._ ⊢> (A <⇒ B))  (m⇒  f g)  = wrap {A <⊢ _}                (flip  m⇒ g) f
      view (._ ⊢> (A <⇒ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇒ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇒ B))  (r⊗⇒ f)    = wrap {(A <⊗ _) <⊢ _}                r⊗⇒   f
      view (._ ⊢> (A <⇒ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇒ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (m⇐  f g)  = wrap {_ ⊢> A}                (flip  m⇐ g) f
      view (._ ⊢> (A <⇐ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇐ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇐ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇐ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (r⊗⇐ f)    = wrap {_ ⊢> A}                       r⊗⇐   f

      wrap : ∀ { I : Contextᴶ + } { J : Contextᴶ + } {B C}
           →  (g : ∀ {G} → NL I [ G ]ᴶ → NL J [ G ]ᴶ) (f : NL I [ B ⇒ C ]ᴶ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g ∘ f′) (cong g pr)

  module ⇐ where

    data Origin {B C} ( J : Contextᴶ + ) (f : NL J [ B ⇐ C ]ᴶ) : Set where
         origin  : ∀ {E F}
                 →  (h₁  : NL B ⊢ E)
                 →  (h₂  : NL F ⊢ C)
                 →  (f′  : ∀ {G} → NL G ⊢ E ⇐ F → NL J [ G ]ᴶ)
                 →  (pr  : f ≡ f′ (m⇐ h₁ h₂))
                 →  Origin J f

    mutual
      view : ∀ {B C} ( J : Contextᴶ + ) (f : NL J [ B ⇐ C ]ᴶ) → Origin J f
      view ([] <⊢ ._)        (m⇐  f g)  = origin f g id refl
      view ([] <⊢ ._)        (r⊗⇒ f)    = wrap {(_ ⊗> []) <⊢ _}               r⊗⇒   f
      view ([] <⊢ ._)        (r⊗⇐ f)    = wrap {([] <⊗ _) <⊢ _}               r⊗⇐   f
      view ((A ⊗> B) <⊢ ._)  (m⊗  f g)  = wrap {B <⊢ _}                (      m⊗ f) g
      view ((A ⊗> B) <⊢ ._)  (r⇒⊗ f)    = wrap {B <⊢ _}                       r⇒⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A ⊗> B)) <⊢ _}         r⊗⇒   f
      view ((A ⊗> B) <⊢ ._)  (r⇐⊗ f)    = wrap {_ ⊢> (_ ⇐> B)}                r⇐⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A ⊗> B) <⊗ _) <⊢ _}         r⊗⇐   f
      view ((A <⊗ B) <⊢ ._)  (m⊗  f g)  = wrap {A <⊢ _}                (flip  m⊗ g) f
      view ((A <⊗ B) <⊢ ._)  (r⇒⊗ f)    = wrap {_ ⊢> (A <⇒ _)}                r⇒⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A <⊗ B)) <⊢ _}         r⊗⇒   f
      view ((A <⊗ B) <⊢ ._)  (r⇐⊗ f)    = wrap {A <⊢ _}                       r⇐⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A <⊗ B) <⊗ _) <⊢ _}         r⊗⇐   f
      view (._ ⊢> (A ⇒> B))  (m⇒  f g)  = wrap {_ ⊢> B}                (      m⇒ f) g
      view (._ ⊢> (A ⇒> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇒> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇒> B))  (r⊗⇒ f)    = wrap {_ ⊢> B}                       r⊗⇒   f
      view (._ ⊢> (A ⇒> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇒> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (m⇐  f g)  = wrap {B <⊢ _}                (      m⇐ f) g
      view (._ ⊢> (A ⇐> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇐> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇐> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇐> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (r⊗⇐ f)    = wrap {(_ ⊗> B) <⊢ _}                r⊗⇐   f
      view (._ ⊢> (A <⇒ B))  (m⇒  f g)  = wrap {A <⊢ _}                (flip  m⇒ g) f
      view (._ ⊢> (A <⇒ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇒ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇒ B))  (r⊗⇒ f)    = wrap {(A <⊗ _) <⊢ _}                r⊗⇒   f
      view (._ ⊢> (A <⇒ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇒ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (m⇐  f g)  = wrap {_ ⊢> A}                (flip  m⇐ g) f
      view (._ ⊢> (A <⇐ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇐ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇐ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇐ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (r⊗⇐ f)    = wrap {_ ⊢> A}                       r⊗⇐   f

      wrap : ∀ { I : Contextᴶ + } { J : Contextᴶ + } {B C}
           →  (g : ∀ {G} → NL I [ G ]ᴶ → NL J [ G ]ᴶ) (f : NL I [ B ⇐ C ]ᴶ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g ∘ f′) (cong g pr)
\end{code}
\end{comment}

\begin{frame}{Cut elimination (revisited)}
\centering\vfill
\begin{code}
  cut′ : ∀ {A B C} → NL A ⊢ B → NL B ⊢ C → NL A ⊢ C

  cut′ {B = el _} f g with el.view ([] <⊢ _) g
  ... | el.origin g′ _ = g′ f

  cut′ {B = _ ⊗ _} f g with ⊗.view (_ ⊢> []) f
  ... | ⊗.origin h₁ h₂ f′ _ =
      f′ (r⇐⊗ (cut′ h₁ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ g))))))
\end{code}
\vdots
\vfill
\note{}
\end{frame}

\begin{comment}
\begin{code}
  cut′ {B = _ ⇒ _} f g with ⇒.view ([] <⊢ _) g
  ... | ⇒.origin h₁ h₂ g′ _ =
    g′ (r⊗⇒ (r⇐⊗ (cut′ h₁ (r⊗⇐ (cut′ (r⇒⊗ f) h₂)))))
  cut′ {B = _ ⇐ _}  f  g with ⇐.view ([] <⊢ _) g
  ... | ⇐.origin h₁ h₂ g′ _ =
    g′ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ (cut′ (r⇐⊗ f) h₁)))))
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  _⊢NL_ : (A B : Type) → Set
  A ⊢NL B = NL A ⊢ B
\end{code}
\end{comment}

\begin{comment}
%<*preorder>
\begin{code}
  isPreorder : IsPreorder _≡_ _⊢NL_
  isPreorder = record
    {  isEquivalence  = ≡.isEquivalence
    ;  reflexive      = λ A=B → subst (_ ⊢NL_) A=B ax′
    ;  trans          = cut′
    }
\end{code}
%</preorder>
\end{comment}

\begin{comment}
\begin{code}
  el-injective : ∀ {A B} → el A ≡ el B → A ≡ B
  el-injective refl = refl

  ⇒-injective : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → A ≡ B × C ≡ D
  ⇒-injective refl = refl , refl

  ⇐-injective : ∀ {A B C D} → A ⇐ C ≡ B ⇐ D → A ≡ B × C ≡ D
  ⇐-injective refl = refl , refl

  ⊗-injective : ∀ {A B C D} → A ⊗ C ≡ B ⊗ D → A ≡ B × C ≡ D
  ⊗-injective refl = refl , refl
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  infix 1 _≟-Type_

  _≟-Type_ : (A B : Type) → Dec (A ≡ B)
  el A  ≟-Type el C with (A ≟-Atom C)
  ... | yes A=C rewrite A=C = yes refl
  ... | no  A≠C = no (A≠C ∘ el-injective)
  el A  ≟-Type C ⊗ D = no (λ ())
  el A  ≟-Type C ⇐ D = no (λ ())
  el A  ≟-Type C ⇒ D = no (λ ())

  A ⊗ B ≟-Type el C  = no (λ ())
  A ⊗ B ≟-Type C ⊗ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _                         = no (A≠C ∘ proj₁ ∘ ⊗-injective)
  ... | _       | no  B≠D                   = no (B≠D ∘ proj₂ ∘ ⊗-injective)
  A ⊗ B ≟-Type C ⇐ D = no (λ ())
  A ⊗ B ≟-Type C ⇒ D = no (λ ())

  A ⇐ B ≟-Type el C  = no (λ ())
  A ⇐ B ≟-Type C ⊗ D = no (λ ())
  A ⇐ B ≟-Type C ⇐ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⇐-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⇐-injective)
  A ⇐ B ≟-Type C ⇒ D = no (λ ())

  A ⇒ B ≟-Type el C  = no (λ ())
  A ⇒ B ≟-Type C ⊗ D = no (λ ())
  A ⇒ B ≟-Type C ⇐ D = no (λ ())
  A ⇒ B ≟-Type C ⇒ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⇒-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⇒-injective)
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  ⊢-injective : ∀ {A B C D} → (A ⊢ B) ≡ (C ⊢ D) → A ≡ C × B ≡ D
  ⊢-injective refl = refl , refl
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  infix 1 _≟-Judgement_

  _≟-Judgement_ : (I J : Judgement) → Dec (I ≡ J)
  (A ⊢ B) ≟-Judgement (C ⊢ D) with A ≟-Type C | B ≟-Type D
  ...| yes A=C | yes B=D = yes (cong₂ _⊢_ A=C B=D)
  ...| no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⊢-injective)
  ...| _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⊢-injective)
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  {-# TERMINATING #-}
  search : {Mon : Set → Set} (monadPlus : RawMonadPlus Mon) (J : Judgement) → Mon (NL J)
  search {Mon} monadPlus = search′ []
    where
    open RawMonadPlus monadPlus using (∅; _∣_; return; _>>=_)

    search′ : (seen : List Judgement) (J : Judgement) → Mon (NL J)
    search′ seen J with any (J ≟-Judgement_) seen
    search′ seen J | yes J∈seen = ∅
    search′ seen J | no  J∉seen
      = check-ax J
      ∣ check-m⊗  J ∣ check-m⇒  J ∣ check-m⇐  J
      ∣ check-r⇒⊗ J ∣ check-r⇐⊗ J ∣ check-r⊗⇒ J ∣ check-r⊗⇐ J
      where


      reset    = search′ []         -- for rules which make progress
      continue = search′ (J ∷ seen) -- for rules which make no progress


      check-ax : (J : Judgement) → Mon (NL J)
      check-ax (el A ⊢ el B) with A ≟-Atom B
      ... | yes A=B rewrite A=B = return ax
      ... | no  A≠B             = ∅
      check-ax _ = ∅

      check-m⊗ : (J : Judgement) → Mon (NL J)
      check-m⊗ (A ⊗ C ⊢ B ⊗ D) =
        reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⊗ x y)
      check-m⊗ _ = ∅

      check-m⇒ : (J : Judgement) → Mon (NL J)
      check-m⇒ (B ⇒ C ⊢ A ⇒ D) =
        reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⇒ x y)
      check-m⇒ _ = ∅

      check-m⇐ : (J : Judgement) → Mon (NL J)
      check-m⇐ (A ⇐ D ⊢ B ⇐ C) =
        reset (A ⊢ B) >>= λ x → reset (C ⊢ D) >>= λ y → return (m⇐ x y)
      check-m⇐ _ = ∅

      check-r⇒⊗ : (J : Judgement) → Mon (NL J)
      check-r⇒⊗ (A ⊗ B ⊢ C) = continue (B ⊢ A ⇒ C) >>= λ x → return (r⇒⊗ x)
      check-r⇒⊗ _  = ∅

      check-r⇐⊗ : (J : Judgement) → Mon (NL J)
      check-r⇐⊗ (A ⊗ B ⊢ C) = continue (A ⊢ C ⇐ B) >>= λ x → return (r⇐⊗ x)
      check-r⇐⊗ _  = ∅

      check-r⊗⇒ : (J : Judgement) → Mon (NL J)
      check-r⊗⇒ (B ⊢ A ⇒ C) = continue (A ⊗ B ⊢ C) >>= λ x → return (r⊗⇒ x)
      check-r⊗⇒ _  = ∅

      check-r⊗⇐ : (J : Judgement) → Mon (NL J)
      check-r⊗⇐ (A ⊢ C ⇐ B) = continue (A ⊗ B ⊢ C) >>= λ x → return (r⊗⇐ x)
      check-r⊗⇐ _  = ∅

  findAll : (J : Judgement) → List (NL J)
  findAll = search Data.List.monadPlus
\end{code}
\end{comment}

\begin{comment}
\begin{code}
module example where
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  infixr 4 _∙_

  data Struct (A : Set) : Set where
    ·_· : A → Struct A
    _∙_ : Struct A → Struct A → Struct A
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  open RawApplicative {{...}} using (_<$>_; _⊛_)
  traverse : ∀ {F A B} {{AppF : RawApplicative F}} → (A → F B) → Struct A → F (Struct B)
  traverse f  ·   x    · = ·_· <$> f x
  traverse f  (l  ∙ r  ) = _∙_ <$> traverse f l ⊛ traverse f r
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  data Atom : Set where
    N   : Atom
    NP  : Atom
    S   : Atom
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  _≟-Atom_ : (A B : Atom) → Dec (A ≡ B)
  N   ≟-Atom N   = yes refl
  N   ≟-Atom NP  = no (λ ())
  N   ≟-Atom S   = no (λ ())
  NP  ≟-Atom N   = no (λ ())
  NP  ≟-Atom NP  = yes refl
  NP  ≟-Atom S   = no (λ ())
  S   ≟-Atom N   = no (λ ())
  S   ≟-Atom NP  = no (λ ())
  S   ≟-Atom S   = yes refl
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  data Word : Set where
    mary       : Word
    finds      : Word
    a          : Word
    unicorn    : Word
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  open non-associative_lambek_calculus Atom _≟-Atom_
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  np n s : Type
  np   = el NP
  n    = el N
  s    = el S
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  Lex : Word → List⁺ Type
  Lex mary     = np ∷ []
  Lex finds    = ((np ⇒ s) ⇐ np) ∷ []
  Lex a        = ((s ⇐ (np ⇒ s)) ⇐ n)
               ∷ ((((np ⇒ s) ⇐ np) ⇒ (np ⇒ s)) ⇐ n)
               ∷ ((((np ⇒ s) ⇐ np) ⇒ ((s ⇐ (np ⇒ s)) ⇒ s)) ⇐ n) ∷ []
  Lex unicorn  = n ∷ []
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  Valid : Struct Type → Set
  Valid Γ = NL ⌊ Γ ⌋ ⊢ s
    where
      ⌊_⌋ : Struct Type → Type
      ⌊ · A · ⌋ =       A
      ⌊ X ∙ Y ⌋ = ⌊ X ⌋ ⊗ ⌊ Y ⌋
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  Parse : Struct Word → Set
  Parse ws = foldr₁ _⊎_ (map⁺ Valid (traverse Lex ws))
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  parse : (ws : Struct Word) → List (Parse ws)
  parse ws with traverse Lex ws
  parse ws | Γ ∷ Γs = parse′ Γ Γs
    where
      parse′ : (Γ : _) (Γs : List _) → List (foldr₁ _⊎_ (map⁺ Valid (Γ ∷ Γs)))
      parse′ Γ       []  = findAll _
      parse′ Γ (Γ′ ∷ Γs) = map inj₁ (findAll _) ++ map inj₂ (parse′ Γ′ Γs)
\end{code}
\end{comment}

\begin{comment}
\begin{code}
  infixr 1 ✓_ *_

  ✓_ : Struct Word → Set
  ✓ ws = T (not (null (parse ws)))

  *_ : Struct Word → Set
  * ws = T (null (parse ws))
\end{code}
\end{comment}

\begin{comment}
%<*example>
\begin{code}
  ex₁ : ✓ · mary · ∙ · finds · ∙ · a · ∙ · unicorn ·
  ex₁ = _

  ex₂ : ✓ (· a · ∙ · unicorn ·) ∙ · finds · ∙ · mary ·
  ex₂ = _

  ex₃ : * · unicorn · ∙ · unicorn · ∙ · unicorn · ∙ · unicorn ·
  ex₃ = _
\end{code}
%</example>
\end{comment}

\end{document}
