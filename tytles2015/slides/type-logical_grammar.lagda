\documentclass[12pt,t]{beamer}

%include agda.fmt
%if False
\usepackage{bbm}%
\let\spec\code%
\let\endspec\endcode%
%endif
\include{preamble}

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
  infix  1 _⊢NL_
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
\begin{itemize}
\item I've always heard it's a good idea to start with your take-home
  message, before all your listeners doze. So here it is:
\item If you want to write highly verified, pretty readable theories
  in linguistics, that is totally possible. Probably.
\item That's what I'll be doing in this talk: I will use Agda to show
  you that I can write a highly verified \textit{and} readable theory
  of, in this case, syntax.
\item That last restriction is not anything fundamental, it's just
  that I'm basing myself in derivational semantics, and therefore we
  cannot really have any semantics without first having syntax. And we
  only have thirty minutes.
\item Anyway, before we start off, I'll give you two examples of what
  I mean with ``highly verified''.
\end{itemize}
}
\end{frame}

\begin{frame}{Example}
\centering\vfill
\ExecuteMetaData{example}
\vfill
{\tiny (The constructors of the parse tree have been omitted, as they are superfluous.)}
\note{%
\begin{itemize}
\item It should be self-evident what these statements mean, even if
  they're in Agda. The first two sentences are OK, the last one is
  ungrammatical.
\item The way I'm using them is not typical: normally they'd be based
  on the innate linguistic competence of native speakers, but here
  they're based on a tiny type-logical grammar embedded in these
  slides.
\item One more neat observation: they are highlighted.
\item In order to appreciate that, you need to know that Agda is a
  dependently-type language, and therefore does not really have a
  distinction between different sorts of things: everything is a
  term. So highlighting is done \textit{semantically}. Therefore, the
  code must type-check. These statements are crafted such that if they
  are false, they result in a type-error.
\item This is what I mean with highly verified: the claims I'm making
  here were checked, and since then I've had no opportunity to
  introduce new mistakes.
\item As an aside, that will be true for the rest of this talk: if
  something is highlighted, that means it's been type-checked.
\end{itemize}
}
\end{frame}


\begin{frame}{Example}
\centering\vfill
\ExecuteMetaData{preorder}
\vfill
{\tiny (I realise this doesn't say much at the moment, but we're getting there.)}
\note{%
I understand that this second example probably doesn't really
parse. But its intended meaning is this: since we are working in
derivational syntax, we generally want the underlying logic to have
some properties. This statement behind me means that we have shown
that the system we will develop later on is in fact a preorder, which
is kind-of the minimum requirement.

It also contains a little hint as to what system we've been using: the
grammaticality judgements in the previous slides were based on the
non-associative Lambek calculus, or NL. And this is the system we'll
spend the rest of this talk formalising.

I mostly chose to formalise NL for the talk because it is so basic
that everyone should already be familiar with it, and it (or
extensions of it) come up very often.

If you look at my paper in the proceedings, you'll see that I'm doing
the same thing for the Lambek-Grishin calculus, and if you'll have a
look at my thesis, you'll find formalisations for many more systems.
}
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
\note{%
\begin{itemize}
\item I'm assuming everyone is familiar with the concept of
  algebraic datatypes. If you're not, I'm sorry. Super short version:
  it's a way of defining a brand new type, together with the only ways
  to construct inhabitants of that type.
\item \AgdaBound{Atom} is abstracted over.
\item We insert \AgdaBound{Atom} into \AgdaFunction{Type} through
  the constructor \AgdaInductiveConstructor{el}.
\item Judgement is used slightly differently, referring to the
  syntactic construct \textit{without} a proof.
\item On the next slide we will define a datatype which is
  parameterised over these syntactic judgements. \textit{That} is
  where the proofs will live.
\end{itemize}
}
\end{frame}

\begin{comment}
\begin{code}
  mutual
    _⊢NL_ : (A B : Type) → Set
    A ⊢NL B = NL A ⊢ B
\end{code}
\end{comment}

\begin{frame}{The non-associative Lambek calculus}
\centering\vfill
\begin{code}
    data NL_ : Judgement → Set where

      ax   : ∀ {A} → el A ⊢NL el A

      m⊗   : ∀ {A B C D} → A ⊢NL B → C ⊢NL D → A ⊗ C ⊢NL B ⊗ D
      m⇒   : ∀ {A B C D} → A ⊢NL B → C ⊢NL D → B ⇒ C ⊢NL A ⇒ D
      m⇐   : ∀ {A B C D} → A ⊢NL B → C ⊢NL D → A ⇐ D ⊢NL B ⇐ C

      r⇒⊗  : ∀ {A B C} → B ⊢NL A ⇒ C → A ⊗ B ⊢NL C
      r⊗⇒  : ∀ {A B C} → A ⊗ B ⊢NL C → B ⊢NL A ⇒ C
      r⇐⊗  : ∀ {A B C} → A ⊢NL C ⇐ B → A ⊗ B ⊢NL C
      r⊗⇐  : ∀ {A B C} → A ⊗ B ⊢NL C → A ⊢NL C ⇐ B
\end{code}
\vfill
{\tiny (Each judgement should be prefixed with \AgdaFunction{NL}, but
  in the interest of readability we will use \AgdaBound{A}
  \AgdaFunction{⊢} \AgdaBound{B} \AgdaSymbol{=} \AgdaDatatype{NL}
  \AgdaBound{A} \AgdaInductiveConstructor{⊢} \AgdaBound{B}.)}
\note{%
\begin{itemize}
\item This datatype is where the actual proofs live.
\item The system is due to Moortgat \& Oehrle (1996).
\item The judgement is a \textit{term} which is present in the
  \textit{type} of \AgdaFunction{NL}.
\item Each judgement should be prefixed with \AgdaFunction{NL},
  but we're leaving this out because of cluttering. Instead we will
  colour the turnstile blue.
\item We are also leaving out all quantifiers.
\item In this system we have both identity expansion and cut elimination.
\end{itemize}
}
\end{frame}


\begin{frame}{Identity expansion}
\centering\vfill
\begin{code}
  ax′ : ∀ {A} → A ⊢NL A
  ax′ {A =  el   A} = ax
  ax′ {A =  A ⊗  B} = m⊗  ax′ ax′
  ax′ {A =  A ⇐  B} = m⇐  ax′ ax′
  ax′ {A =  A ⇒  B} = m⇒  ax′ ax′
\end{code}
\vfill
{\tiny ($\AgdaSymbol{\{}\AgdaArgument{A} \AgdaSymbol{=} \AgdaBound{...}\AgdaSymbol{\}}$ is Agda syntax to match on implicit parameters.)}
\note{%
\begin{itemize}
\item An easy first proof is that of identity expansion: from
  restricting the \AgdaInductiveConstructor{ax} rule to atomic
  formulas, we can recover the full identity.
\item $\AgdaSymbol{\{}\AgdaArgument{A} \AgdaSymbol{=}
  \AgdaBound{...}\AgdaSymbol{\}}$ is Agda syntax to match on implicit
  parameters.
\end{itemize}
}
\end{frame}

\begin{frame}{Cut elimination}
\vfill
\begin{itemize}
\item
  All connectives are introduced by monotonicity rules.

\item
  Each connective can be affected by residuation at the top-level
  on only \textit{one} side of the turnstile.

\item
  In a cut, we have the top-level connective available on
  \textit{both} sides.

\item
  So: we can be sure to find the monotonicity rule which introduced
  the connective in one of the arguments.
\end{itemize}
\vfill
\note{%
\begin{itemize}
\item This is a corrected and simplified version of the original
  proof. When I originally formalised the proof, it didn't
  type-check. Then, when I had fixed it, I could delete over half the
  cases in the original proof.
\item Cut elimination is based on the following crucial insights:
  \begin{itemize}
  \item All connectives are introduced by monotonicity rules.
  \item Each connective can be affected by residuation at the
    top-level on only \textit{one} side of the turnstile.
  \item In a cut, we have the top-level connective available on
    \textit{both} sides.
  \item So: we can be sure to find the monotonicity rule which
    introduced the connective in one of the arguments.
  \end{itemize}
\item We can replace the monotonicity rule with two smaller cuts,
  chained together with residuation rules.
\end{itemize}
}
\end{frame}

\begin{comment}
\begin{code}
  module ⊗′ where
\end{code}
\end{comment}

\begin{frame}{Cut elimination}
For instance, in the case of ⊗:\\
\vfill\noindent
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
\vfill
\note{%
\begin{itemize}
\item For instance, this is the rewrite schema for the product.
\item You can fill in the terms yourself:
  \begin{itemize}
  \item On the left-hand side, you see a monotonicity rule followed by
    some arbitrary sequence of rules, followed by a cut.
  \item On the right-hand side you see F-C then E-B being cut `into'
    the proof, while residuation rules are used to `shuffle' the terms
    around such that cutting is possible.
  \end{itemize}
\item So these rewrite steps are simple enough\ldots But! Since ``we
  can always find the monotonicity rule which introduced the
  connective'' is a pretty self-evident claim , the original paper
  spends no more words on this.
\item This turns out to be where most of our computation is.
\item Let's have a look at the ``monotonicity rule which introduced
  the connective'' in our example. We'll refer to this as the `origin'
  of the connective.
\end{itemize}
}
\end{frame}

\begin{frame}{Origins}
\vfill
\only<1>{%
\begin{prooftree}
\AXC{$E           \vdash B          $}
\AXC{$          F \vdash           C$}
\BIC{$E \otimes F \vdash B \otimes C$}
\UIC{$            \vdots            $}
\UIC{$A           \vdash B \otimes C$}
\end{prooftree}
}
\only<2>{%
\begin{prooftree}
\AXC{\AgdaBound{$h_1$} \AgdaSymbol{:} $ E \vdash B$}
\AXC{\AgdaBound{$h_2$} \AgdaSymbol{:} $ F \vdash C$}
\BIC{\AgdaInductiveConstructor{m⊗} \AgdaBound{$h_1$} \AgdaBound{$h_2$} \AgdaSymbol{:} $E \otimes F \vdash B \otimes C$}
\UIC{\AgdaBound{f′} \AgdaSymbol{:} $\vdots$}
\UIC{\AgdaBound{f′} \AgdaSymbol{(}\AgdaInductiveConstructor{m⊗} \AgdaBound{$h_1$} \AgdaBound{$h_2$}\AgdaSymbol{)} \AgdaSymbol{:} $A \vdash B \otimes C$}
\end{prooftree}
}
\vfill
\note{%
\begin{itemize}
\item Before we can formalise the claim that we can always find the
  origin, we must have a concept of an origin.
\item Let's fill in the terms. We have two primitive terms $h_1$ and
  $h_2$, and a function $f′$ which takes the product of them, so to
  speak, to whatever we had.
\item We can represent that as follows.
\end{itemize}
}
\end{frame}

\begin{frame}{Origins}
\centering\vfill
\begin{code}
    data  Origin′ {A B C}
          ( f : A ⊢NL B ⊗ C )
          : Set where

          origin  : ∀ {E F} →  (h₁  : E ⊢NL B)
                  →            (h₂  : F ⊢NL C)
                  →            (f′  : ∀ {G} → E ⊗ F ⊢NL G → A ⊢NL G)
                  →            (pr  : f ≡ f′ (m⊗ h₁ h₂))
                  →            Origin′ f
\end{code}
\vfill
{\tiny (Function \AgdaBound{f′} should work for \textit{any} type \AgdaBound{G}.)}
\note{%
\begin{itemize}
\item An origin is a datatype which is parameterised over a
  \textit{proof} $f$ (note the blue) with a product on the right-hand
  side of the turnstile.
\item We have two sub-proofs $h_1$ and $h_2$, and the function $f′$,
  as before.
\item One notable change is in the type of $f′$, where a \AgdaBound{G}
  has appeared. This is because we want to use it not only for the
  case of $B ⊗ C$, but also in the result, where it will apply to
  something with a $D$ there.
\item In addition, we have an element $pr$, which is a witness to the
  fact that \AgdaBound{f′} \AgdaSymbol{(}\AgdaInductiveConstructor{m⊗}
  \AgdaBound{$h_1$} \AgdaBound{$h_2$}\AgdaSymbol{)} is equal to our
  original proof $f$---a witness to the correctness of our origin.
\item If we have an inhabitant of this datatype, and a proof $g$ with
  the same product on the left-hand side, we are able to rewrite this
  to a proof with two smaller cuts.
\end{itemize}
}
\end{frame}

\begin{frame}{Origins}
\vfill
\only<1>{%
\begin{prooftree}
\AXC{$               E           \vdash B                       $}
\AXC{$                         F \vdash           C             $}
\BIC{$               E \otimes F \vdash B \otimes C             $}
\UIC{$                           \vdots                         $}
\UIC{$               A \otimes D \vdash B \otimes C             $}
\end{prooftree}
}
\only<2>{%
\begin{prooftree}
\AXC{$                                  E           \vdash  B                       $}
\AXC{$                                            F \vdash            C             $}
\BIC{$                                  E \otimes F \vdash  B \otimes C             $}
\UIC{$                                              \vdots                          $}
\UIC{$ \color{AgdaInductiveConstructor} A           \vdash (B \otimes C) \varslash D$}
\UIC{$                                  A \otimes D \vdash  B \otimes C             $}
\end{prooftree}
}
\vfill
\note{%
\begin{itemize}
\item We would like to recursively construct this instance, by stepping
  up through the proof, remembering everything (for $f′$) and then in
  the end when we stumble upon the origin, return an Origin. But!
\item *click*
\item What if the first step is for instance this residuation rule?
  Now we no longer have a product on the right-hand side!
\item For the implications (and for all connectives in the
  Lambek-Grishin calculus) the problem is even bigger. Because these
  can even, temporarily, move to the \textit{other side of the
  turnstile}.
\item So, back to the drawing board: we need some way of expressing
  the contexts under which a type may occur such that residuation
  brings it to the top-level on the right side.
\end{itemize}
}
\end{frame}

\begin{frame}{Contexts}
\centering\vfill
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
\vfill
\note{%
\begin{itemize}
\item We will define a polarity type: positive or input and negative
  or output polarities.
\item Each connective has a polarity associated with it. Let's not get
  too deeply into that, but let's just say that ⊗ is positive because
  it can be affected by residuation on the left-hand side, and its
  arguments are positive because residuation will drop them on the
  left-hand side.
\item The first polarity is the polarity of the hole, all the way down
  in the context. The second polarity is the polarity of the
  expression itself.
\item If we put the context on the side governed by the second
  polarity, then residuation can `remove' it, and leave whatever was
  plugged into the hole on the side governed by the first polarity.
\end{itemize}
}
\end{frame}

\begin{frame}{Contexts}
\centering\vfill
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
\vfill
\note{%
\begin{itemize}
\item Boilerplate! Sorry about this, but I just wanted it to be in the
  slides for completeness.
\item Anyway, this is the plugging function. It takes one of these
  contexts, and plugs a type into the hole.
\end{itemize}
}
\end{frame}

\begin{frame}{Contexts}
\centering\vfill
\begin{code}
  data Contextᴶ (p : Polarity) : Set where
    _<⊢_  : Context p +  → Type         → Contextᴶ p
    _⊢>_  : Type         → Context p -  → Contextᴶ p

  _[_]ᴶ : ∀ {p} → Contextᴶ p → Type → Judgement
  A <⊢ B [ C ]ᴶ = A [ C ] ⊢ B
  A ⊢> B [ C ]ᴶ = A ⊢ B [ C ]
\end{code}
\vfill
\note{%
\begin{itemize}
\item Since we have syntactic judgements, we can do the same trick for
  judgements.
\item One difference is that obviously the outer polarity is clear
  from the side of the turnstile you pick.
\end{itemize}
}
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

          origin  : ∀ {E F} →  (h₁  : E ⊢NL B)
                  →            (h₂  : F ⊢NL C)
                  →            (f′  : ∀ {G} → E ⊗ F ⊢NL G → NL J [ G ]ᴶ)
                  →            (pr  : f ≡ f′ (m⊗ h₁ h₂))
                  →            Origin J f
\end{code}
\vfill
\note{%
Back to our definition for origin:
\begin{itemize}
\item We are going to replace the type to no longer say ``needs to be
  a product in the right-hand side at top-level'' but to say ``needs
  to be a product such that it could end up in the right-hand side at
  the top-level''.
\item This basically means that it is the top-most connective such that
  it is not affected by residuation.
\end{itemize}
}
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
\note{%
\begin{itemize}
\item Using this definition of \AgdaFunction{Origin} our recursion
  \textit{does} work out.
\item I'm not showing you all the cases here, though, because there's
  29 of them. And it's basically just simple induction.
\item \textbf{If time}: the reason for this is that I'm now writing
  the type of \AgdaBound{f} with a \textit{function} in there. In
  order to pattern match on \AgdaBound{f}, we first have to know which
  patterns are valid, and in order to know that we have to know what
  the plugging reduces to.
\item The wrapping function simply calls \AgdaFunction{view}
  recursively on \AgdaBound{f}, breaks open the returned origin, and
  updates it by wrapping the given function around it.
\item *click*
\item So really, it looks scarier than it is.
\item It is really worth mentioning here that a \AgdaKeyword{with}
  pattern is basically a case statement. So you're just pattern
  matching there. And then \AgdaBound{g} is used twice because we have
  to update the function (the vertical dots) and the proof of
  correctness.
\item So anyway, we need to define these \AgdaFunction{Origin} and
  \AgdaFunction{view} things for each connective. It's a little
  tedious.
\item \textbf{If time}: if we put a little bit more effort into this,
  we could formalise e.g. display calculus, and use this to abstract
  over connectives. Then we'd really only have to do this once.
\end{itemize}
}
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
      wrap  : ∀ { I : Contextᴶ - } { J : Contextᴶ - } {B C}  (g : ∀ {G} → NL I [ G ]ᴶ → NL J [ G ]ᴶ) (f : NL I [ B ⊗ C ]ᴶ)
            → Origin J (g f)
      wrap {I} {J} g f with view I f
      wrap {I} {J} g f | origin h₁ h₂ f′ pr = origin h₁ h₂ (g ∘ f′) (cong g pr)
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
\vfill
\begin{varwidth}{\linewidth}
\begin{code}
  cut′ : ∀ {A B C} → A ⊢NL B → B ⊢NL C → A ⊢NL C
\end{code}
\only<1>{\newline}%
\begin{code}
  cut′ {B = el _} f g with el.view ([] <⊢ _) g
  ... | el.origin g′ _ = g′ f
\end{code}
\only<1>{\newline}%
\begin{code}
  cut′ {B = _ ⊗ _} f g with ⊗.view (_ ⊢> []) f
  ... | ⊗.origin h₁ h₂ f′ _ =
      f′ (r⇐⊗ (cut′ h₁ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ g))))))
\end{code}
\only<1>{\centering\vdots}%
\only<2>{%
\begin{code}
  cut′ {B = _ ⇒ _} f g with ⇒.view ([] <⊢ _) g
  ... | ⇒.origin h₁ h₂ g′ _ =
    g′ (r⊗⇒ (r⇐⊗ (cut′ h₁ (r⊗⇐ (cut′ (r⇒⊗ f) h₂)))))
  cut′ {B = _ ⇐ _} f g with ⇐.view ([] <⊢ _) g
  ... | ⇐.origin h₁ h₂ g′ _ =
    g′ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ (cut′ (r⇐⊗ f) h₁)))))
\end{code}
}
\end{varwidth}
\vfill
\note{%
\begin{itemize}
\item So now we can write a cut elimination procedure.
\item First we have the type signature.
\item The second group we haven't really talked about, but that's the
  base case. If we cut on an atomic formula, then the origin is an
  \AgdaInductiveConstructor{ax} rule, and we can simply insert the
  rest of the proof there.
\item The third group is the case for the product: we find the origin
  using \AgdaFunction{view}, pattern match using \AgdaKeyword{with},
  and apply the rewrite schema---now for the first time in Agda!
\item This is structurally recursive, because we call
  \AgdaFunction{cut′} with a structurally smaller type \AgdaBound{B}.
\item And those vertical dots there seem to imply there is much more,
  but it really is only two more cases. I just wanted to have more
  room to just show these two cases, because a slide full of code can
  be overwhelming. But in case you're wondering...
\item *click*
\item Yes, it fits on a single slide.
\end{itemize}
}
\end{frame}

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

\begin{frame}
\vfill%
\includegraphics[width=\linewidth]{ufondslogo.jpg}
\end{frame}

\end{document}
