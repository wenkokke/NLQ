\documentclass[a4paper]{llncs}

%include main.fmt
%format forAll = "\forall"
%format exists = "\exists"
%format ʟᴏᴠᴇs  = "\textsc{loves}"
%format ᴘᴇʀsᴏɴ = "\textsc{person}"
%format sᴇɴᴛ₀  = "\textsc{sent}_{0}"
%format sᴇɴᴛ₁  = "\textsc{sent}_{1}"
%format sᴇɴᴛ₂  = "\textsc{sent}_{2}"
%format sᴇɴᴛ₃  = "\textsc{sent}_{3}"
%format sᴇɴᴛ₄  = "\textsc{sent}_{4}"
%format sᴇɴᴛ₅  = "\textsc{sent}_{5}"
%format sᴇɴᴛ₆  = "\textsc{sent}_{6}"
%format -->    = "\mapsto"
\include{preamble}

\begin{document}

\title{Formalising type-logical grammars in Agda}%
\author{Pepijn Kokke}%
\institute{Utrecht University}%
\maketitle

\begin{abstract}
In recent years, the interest in using proof assistants to formalise
and reason about mathematics and programming languages has grown.
Type-logical grammars, being closely related to type theories and
systems used in functional programming, are a perfect candidate to
next apply this curiosity to.
The advantages of using proof assistants is that they allow one to
write formally verified proofs about one's type-logical systems, and
that any theory, once implemented, can immediately be computed with.
The downside is that in many cases the formal proofs are written as an
afterthought, are incomplete, or use obtuse syntax.
This makes it that the verified proofs are often much more difficult
to read than the pen-and-paper proofs, and almost never directly
published.
In this paper, we will try to remedy that by example.

Concretely, we use Agda to model the Lambek-Grishin calculus, a
grammar logic with a rich vocabulary of type-forming operations.
We then present a verified procedure for cut elimination in this
system. Then we briefly outline a continuation-passing style
translation from proofs in the Lambek-Grishin calculus to programs in
Agda. And finally, we will put our system to use in the analysis of a
simple example sentence.
\end{abstract}

\begin{hide}
\begin{code}
-- This file contains the code from the paper "Formalising
-- type-logical grammars in Agda", and was directly extracted from the
-- paper's source.
--
-- Note: because the symbol customarily used for the "left difference"
-- is unavailable in the Unicode character set, and the backslash used
-- for implication is often a reserved symbol, the source file uses a
-- different notation for the connectives: the left and right
-- implications are represented by the double arrows "⇐" and "⇒", and
-- the left and right differences are represented by the triple arrows
-- "⇚" ad "⇛".

module main where
\end{code}
\end{hide}

\begin{hide}
\begin{code}
open import Function                              using (id; flip; _∘_)
open import Data.Bool                             using (Bool; true; false; _∧_)
open import Data.Empty                            using (⊥)
open import Data.Product                          using (_×_; _,_)
open import Data.Unit                             using (⊤)
open import Reflection                            using (Term; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable            using (⌊_⌋)
\end{code}
\end{hide}


\section{Introduction}

Why would we want to formalise type-logical grammars using proof
assistants? One good reason is that it allows us to write formally
verified proofs about the theoretical properties of our type-logical
grammars. But not only that---it allows us to directly run our proofs
as programs. For instance, we can directly run the procedure for cut
elimination in this paper to investigate what kind of derivations are
created by it \textit{and} be confident in its correctness.

Why, then, would we want to use Agda instead of a more established
proof assistant such as, for instance, Coq? There are several good
reasons, but we believe that the syntactic freedom offered by Agda is
the most important.
It is this freedom that allows us to write machine-checkable proofs,
formatted in a way which is very close to the way one would otherwise
typeset proofs, and which are highly readable compared to other
machine-checked proofs.
This means that we can be confident that the proofs \textit{as they
are published} are correct, and that they are necessarily complete---for
though we can hide some of the less interesting definitions from the
final paper, we cannot omit them from the source.

Additionally, because there is a one-to-one correspondence between the
published proofs and the code, it becomes very easy for the reader to
start up a proof environment and inspect the proofs interactively in
order to further their understanding.


Our test case in this paper is the Lambek-Grishin calculus \citep[LG,
][]{moortgat2009}. LG is an example of an extended Lambek calculus. In
addition to the product (|⊗|) and the residual slashes (|⇒|, |⇐|), LG
has a dual family with |⊕| and difference operations (|⇚|, |⇛|)
together with distributivity principles for the interaction between
the two families. See \citet{moortgat2009} for discussion of how LG
overcomes syntactic and semantic limitations of the original Lambek
calculus.

We will formalise the residuation-monotonicity axiomatisation for the
Lambek-Grishin calculus~\citep{moortgat2007} in Agda, present a
verified procedure for cut elimination in this system, and briefly
outline a continuation-passing style (CPS) translation into
Agda. There are several reasons why we have chosen to formalise this
particular system.
\begin{itemize}
\item%
  It allows cut as an admissible rule, i.e.\ a function on proofs,
  instead of defining a separate cut-free system and a cut-elimination
  procedure;
\item%
  it has efficiently decidable proof search, largely due to the
  absence of the cut rule;
\item%
  it has some interesting symmetries, as explored in
  \citet{moortgat2007,moortgat2009}. Because of this, most proofs of
  properties of LG are not much more complicated than their associated
  proofs for the non-associative Lambek calculus;
\item
  it has a continuation-passing style interpretation, which has shown to
  be useful in both derivational and lexical semantics
  (\citeauthor{moortgat2007,bs2015,asher2011});
\item%
  lastly, an implementation of the non-associative Lambek calculus can
  easily and mechanically be extracted from our implementation of LG.
\end{itemize}
Since this paper is by no means a complete introduction to Agda or to
dependently-typed programming, we advise the interested reader to
refer to \citet{norell2009} for a detailed discussion of Agda.

It should be mentioned that (although we omit some of the more tedious
parts) this paper is written in literate Agda, and the code has been
made available on GitHub.\footnote{
See \url{https://gist.github.com/pepijnkokke/cc12b92a8a60696b712c\#file-main-agda}.
}


\section{Formulas, Judgements, Base System}

If we want to model our type-logical grammars in Agda, a natural
starting point would be our atomic formulas---such as |n|, |np|, |s|,
etc. These could easily be represented as an enumerated data
type. However, in order to avoid committing to a certain set of atomic
formulas and side-step the debate on which formulas \textit{should} be
atomic, we will simply assume there is a some data type representing
our atomic formulas. This will be reflected in our module header as
follows:
\begin{code}
module logic (Atom : Set) where
\end{code}
Our formulas can easily be described as a data type, injecting our
atomic formulas by means of the constructor |el|, and adding the
familiar connectives from the Lambek-Grishin calculus as binary
constructors. Note that, in Agda, we can use underscores in
definitions to denote argument positions. This means that |_⊗_| below
defines an infix, binary connective:
\begin{code}
  data Type : Set where
    el           : Atom  → Type
    _⊗_ _⇒_ _⇐_  : Type  → Type  → Type
    _⊕_ _⇚_ _⇛_  : Type  → Type  → Type
\end{code}
In the same manner, we can define a data type to represent judgements:
\begin{code}
  data Judgement : Set where
    _⊢_  : Type → Type → Judgement
\end{code}
Using the above definitions, we can now write judgements such as |A ⊗
A ⇒ B ⊢ B| as Agda values.
\begin{hide}
\begin{code}
  infix  1 LG_
  infix  2 _⊢_
  infixl 3 _[_]
  infixl 3 _[_]ᴶ
  infixr 4 _⊗_
  infixr 5 _⊕_
  infixl 6 _⇚_
  infixr 6 _⇛_
  infixr 7 _⇒_
  infixl 7 _⇐_
\end{code}
\end{hide}
Next we will define a data type to represent our logical system. This
is where we can use the dependent type system to our advantage. The
constructors for our data type will represent the axiomatic inference
rules of the system, and their \textit{types} will be constrained by
judgements. Below you can see the entire system LG as an Agda data
type\footnote{
  For the typeset version of this paper we omit the quantifiers for
  all implicit, universally quantified arguments.
}:
\begin{code}
  data LG_ : Judgement → Set where

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
Note that Agda allows arbitrary unicode characters in identifiers, so
|r⊗⇒| is a valid Agda identifier.

Using this data type, we can already do quite a lot. For instance, we
can show that while the inference rule |ax| above is restricted to
atomic formulas\footnote{%
  Whereas the rule |ax| may appear to be unrestricted, it only allows
  the derivation of the identity proof for any formula |el A|. That
  is, any \textit{atomic formula} |A| delimited by the constructor
  |el|.
}, the unrestricted version is admissible, by induction on
the formula. Note that the construction |{A = ...}| below is used to
pattern match on the implicit variable |A|:
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
Alternatively, we could derive the various applications and
co-applications that hold in the Lambek-Grishin calculus:
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
However, the most compelling reason to use the axiomatisation we have
chosen, using residuation and monotonicity rules, is that cut becomes
an admissible rule.



\section{Admissible Cut}

We would like to show that |cut′| of type |LG A ⊢ B → LG B ⊢ C → LG A ⊢ C| is
an admissible rule.
The method of \citet{moortgat1999}, for the basic non-associative
Lambek calculus, can be readily generalized to the case of LG:
\begin{enumerate}[label= (\roman*)]
\item\label{p1} every connective is introduced \textit{symmetrically} by a
  monotonicity rule or as an axiom;
\item\label{p2} every connective has one side (antecedent or succedent) where,
  if it occurs there at the top level, it cannot be taken apart or
  changed by any inference rule;
\item\label{p3} as a consequence of~\ref{p2}, every formula has one
  side where, if it occurs there at the top level, it is immutable,
  i.e.\ there is no rule   which can eliminate it;
\item\label{p4} due to~\ref{p1} and~\ref{p3}, when we find such an
  immutable formula, we can be sure that, stepping through the
  derivation, after some number of steps we will find the monotonicity
  rule which introduced that formula;
\item\label{p5} due to the type of |cut′|, when we match on the cut
  formula |B| we will always have an immutable variant of that formula
  in either the first or the second argument of |cut′|;
\item\label{p6} finally, for each main connective there exists a
  rewrite rule which makes use of the facts in~\ref{p4} and~\ref{p5}
  to rewrite an application of |cut′|: to two applications of |cut′|
  on the arguments of the monotonicity rule which introduced the
  connective, chained together by applications of residuation (for
  binary connectives) or simply to a derivation (for atomic
  formulas).  As an example, the rewrite rule for |_⊗_| can be found
  in figure~\ref{cut:otimes}.
\end{enumerate}
\begin{figure*}[ht]%
  \footnotesize
  \hspace*{ -\parindent }%
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
\caption{Rewrite rule for cut on formula |B ⊗ C|.}
\label{cut:otimes}
\end{figure*}
We can model the view on the left-hand side of the rewrite rule in
figure~\ref{cut:otimes} as a data type.
In order to construct this view for some suitable derivation |f|, we
need two derivations, |h₁| and |h₂| and a derivation |f′|, which
represents the arbitrary derivation steps taking |(m⊗ h₁ h₂)| back to
|f|. Lastly, we include a proof |pr| of the fact that the
reconstructed derivation |f′ (m⊗ h₁ h₂)| is identical to |f|:
\begin{spec}
  data Origin (f   : LG A ⊢ B ⊗ C) : Set where
    origin :  (h₁  : LG E ⊢ B)
              (h₂  : LG F ⊢ C)
              (f′  : ∀ {G} → LG E ⊗ F ⊢ G → LG A ⊢ G)
              (pr  : f ≡ f′ (m⊗ h₁ h₂))
                   → Origin f
\end{spec}
In the above snippet, we have chosen to leave the quantifier |∀ {G}|
explicit to stress that |f′| should work for \textit{any} formula |G|,
not only for |B ⊗ C|.

All that remains now is to show that for any |f| of type |LG A ⊢ B ⊗
C|, we can construct such a view. We will attempt to do this by
induction on the given derivation.
Note that |hole0| is the Agda syntax for a proof obligation. For
clarity, I have added the types of the various subproofs |f| in
comments:
\begin{spec}
  find : (f : LG A ⊢ B ⊗ C) → Origin f
  find (m⊗   f g)  = origin f g id refl
  find (r⇒⊗  f)    = hole0 -- f : LG A₂ ⊢ A₁ ⇒ B ⊗ C
  find (r⇐⊗  f)    = hole1 -- f : LG A₁ ⊢ B ⊗ C ⇐ A₂
  find (r⊕⇛  f)    = hole2 -- f : LG A₂ ⊢ A₁ ⊕ B ⊗ C
  find (r⊕⇚  f)    = hole3 -- f : LG A₁ ⊢ B ⊗ C ⊕ A₂
\end{spec}
Alas! While in the first case, where |f| is of the form |m⊗ f g|, we
have found our monotonicity rule, the remaining cases are less kind.
It seems that we have neglected to account for derivations where our
cut formula is temporarily nested within another formula.

We will need some new vocabulary to describe what is going on in the
above example.
We would like to describe contexts which a) can be taken apart using
residuation, and b) when fully taken apart, will leave the nested
formula on the correct side of the turnstile. A natural fit for this
is using polarity:
\begin{code}
  data Polarity : Set where + - : Polarity
\end{code}
Below we define well-polarised formula and judgement contexts with
exactly one hole. We use a $\triangleleft$ or $\triangleright$ to
denote in which argument the hole is:
\begin{code}
  data Context (p : Polarity) : Polarity → Set where

    []    : Context p p

    _⊗>_  : Type  → Context p +  → Context p +
    _⇒>_  : Type  → Context p -  → Context p -
    _⇐>_  : Type  → Context p +  → Context p -

    _<⊗_  : Context p +  → Type  → Context p +
    _<⇒_  : Context p +  → Type  → Context p -
    _<⇐_  : Context p -  → Type  → Context p -

    _⊕>_  : Type  → Context p -  → Context p -
    _⇚>_  : Type  → Context p -  → Context p +
    _⇛>_  : Type  → Context p +  → Context p +

    _<⊕_  : Context p -  → Type  → Context p -
    _<⇚_  : Context p +  → Type  → Context p +
    _<⇛_  : Context p -  → Type  → Context p +

  data Contextᴶ (p : Polarity) : Set where

    _<⊢_  : Context p +  → Type  → Contextᴶ p
    _⊢>_  : Type  → Context p -  → Contextᴶ p
\end{code}
We also define two operators which, given a context and a formula,
will fill the hole in the given context with the given formula. The
definition for |_[_]| is entirely predictable and repetitive, and has
been mostly omitted\footnote{
  For the remainder of this paper, any partial omission of a function
  will be denoted with an ellipsis at the end of the code block.
}:
\setboolean{partial}{true}%
\begin{code}
  _[_] : ∀ {p₁ p₂} → Context p₁ p₂ → Type → Type
  []        [ A ] = A
  (B ⊗> C)  [ A ] = B ⊗ (C [ A ])
\end{code}
\setboolean{partial}{false}%
\begin{hide}
\begin{code}
  (C <⊗ B)  [ A ] = (C [ A ]) ⊗ B
  (B ⇒> C)  [ A ] = B ⇒ (C [ A ])
  (C <⇒ B)  [ A ] = (C [ A ]) ⇒ B
  (B ⇐> C)  [ A ] = B ⇐ (C [ A ])
  (C <⇐ B)  [ A ] = (C [ A ]) ⇐ B
  (B ⊕> C)  [ A ] = B ⊕ (C [ A ])
  (C <⊕ B)  [ A ] = (C [ A ]) ⊕ B
  (B ⇚> C)  [ A ] = B ⇚ (C [ A ])
  (C <⇚ B)  [ A ] = (C [ A ]) ⇚ B
  (B ⇛> C)  [ A ] = B ⇛ (C [ A ])
  (C <⇛ B)  [ A ] = (C [ A ]) ⇛ B
\end{code}
\end{hide}
\begin{code}
  _[_]ᴶ : ∀ {p} → Contextᴶ p → Type → Judgement
  (A <⊢ B) [ C ]ᴶ = A [ C ] ⊢ B
  (A ⊢> B) [ C ]ᴶ = A ⊢ B [ C ]
\end{code}
The crucial point about these well-polarised judgement contexts is
that, once the entire context is peeled away, the formula will be
at the top level on the side corresponding to the polarity
argument---with $+$ and $-$ corresponding to the antecedent and the
succedent, respectively. Therefore, in order to generalise our
previous definition of |Origin|, we want the occurrence of |B ⊗ C| to
be nested in a \textit{negative} context:
\begin{hide}
\begin{code}
  module ⊗ where
\end{code}
\end{hide}
\begin{code}
    data Origin′ {B C} (J    : Contextᴶ -)
                 (f   : LG J [ B ⊗ C ]ᴶ)
                      : Set where

      origin :   ∀ {E F} (h₁  : LG E ⊢ B)
                 (h₂  : LG F ⊢ C)
                 (f′  : ∀ {G} → LG E ⊗ F ⊢ G → LG J [ G ]ᴶ)
                 (pr  : f ≡ f′ (m⊗ h₁ h₂))
                      → Origin′ J f
\end{code}
Using this more general definition |Origin′|, we can define a more general
function |find′|---and this time, our proof by induction works!

Note that in Agda, the |with| construct is used to pattern match on
the result of an expression:
\begin{hide}
\begin{code}
    mutual
\end{code}
\end{hide}
\setboolean{partial}{true}%
\begin{code}
      find′ : ∀ {B C} (J : Contextᴶ -) (f : LG J [ B ⊗ C ]ᴶ) → Origin′ J f
      find′ (._ ⊢> [])        (m⊗   f g)   = origin f g id refl
      find′ (._ ⊢> (A <⇐ _))  (r⊗⇐  f)     with find′ (_ ⊢> A) f
      ... | origin h₁ h₂ f′ pr rewrite pr  = origin h₁ h₂ (r⊗⇐ ∘ f′) refl
      find′ (._ ⊢> (_ ⇒> B))  (r⊗⇒  f)     with find′ (_ ⊢> B) f
      ... | origin h₁ h₂ f′ pr rewrite pr  = origin h₁ h₂ (r⊗⇒ ∘ f′) refl
\end{code}
\setboolean{partial}{false}%
\begin{hide}
\begin{code}
      find′ ((A <⊗ _) <⊢ ._)  (m⊗  f g)  = go (A <⊢ _)               f (flip m⊗ g)
      find′ ((_ ⊗> B) <⊢ ._)  (m⊗  f g)  = go (B <⊢ _)               g (m⊗ f)
      find′ (._ ⊢> (_ ⇒> B))  (m⇒  f g)  = go (_ ⊢> B)               g (m⇒ f)
      find′ (._ ⊢> (A <⇒ _))  (m⇒  f g)  = go (A <⊢ _)               f (flip m⇒ g)
      find′ (._ ⊢> (_ ⇐> B))  (m⇐  f g)  = go (B <⊢ _)               g (m⇐ f)
      find′ (._ ⊢> (A <⇐ _))  (m⇐  f g)  = go (_ ⊢> A)               f (flip m⇐ g)
      find′ (A <⊢ ._)         (r⊗⇒ f)    = go ((_ ⊗> A) <⊢ _)        f r⊗⇒
      find′ (._ ⊢> (A <⇒ _))  (r⊗⇒ f)    = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find′ ((_ ⊗> B) <⊢ ._)  (r⇒⊗ f)    = go (B <⊢ _)               f r⇒⊗
      find′ ((A <⊗ _) <⊢ ._)  (r⇒⊗ f)    = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find′ (._ ⊢> B)         (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> B))        f r⇒⊗
      find′ (A <⊢ ._)         (r⊗⇐ f)    = go ((A <⊗ _) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (_ ⇐> B))  (r⊗⇐ f)    = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find′ ((_ ⊗> B) <⊢ ._)  (r⇐⊗ f)    = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find′ ((A <⊗ _) <⊢ ._)  (r⇐⊗ f)    = go (A <⊢ _)               f r⇐⊗
      find′ (._ ⊢> B)         (r⇐⊗ f)    = go (_ ⊢> (B <⇐ _))        f r⇐⊗
      find′ ((A <⇚ _) <⊢ ._)  (m⇚  f g)  = go (A <⊢ _)               f (flip m⇚ g)
      find′ ((_ ⇚> B) <⊢ ._)  (m⇚  f g)  = go (_ ⊢> B)               g (m⇚ f)
      find′ ((A <⇛ _) <⊢ ._)  (m⇛  f g)  = go (_ ⊢> A)               f (flip m⇛ g)
      find′ ((_ ⇛> B) <⊢ ._)  (m⇛  f g)  = go (B <⊢ _)               g (m⇛ f)
      find′ (._ ⊢> (A <⊕ _))  (m⊕  f g)  = go (_ ⊢> A)               f (flip m⊕ g)
      find′ (._ ⊢> (_ ⊕> B))  (m⊕  f g)  = go (_ ⊢> B)               g (m⊕ f)
      find′ (A <⊢ ._)         (r⇚⊕ f)    = go ((A <⇚ _) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (_ ⊕> B))  (r⇚⊕ f)    = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (A <⊕ _))  (r⇚⊕ f)    = go (_ ⊢> A)               f r⇚⊕
      find′ ((A <⇚ _) <⊢ ._)  (r⊕⇚ f)    = go (A <⊢ _)               f r⊕⇚
      find′ ((_ ⇚> B) <⊢ ._)  (r⊕⇚ f)    = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find′ (._ ⊢> B)         (r⊕⇚ f)    = go (_ ⊢> (B <⊕ _))        f r⊕⇚
      find′ (A <⊢ ._)         (r⇛⊕ f)    = go ((_ ⇛> A) <⊢ _)        f r⇛⊕
      find′ (._ ⊢> (_ ⊕> B))  (r⇛⊕ f)    = go (_ ⊢> B)               f r⇛⊕
      find′ (._ ⊢> (A <⊕ _))  (r⇛⊕ f)    = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find′ ((A <⇛ _) <⊢ ._)  (r⊕⇛ f)    = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._)  (r⊕⇛ f)    = go (B <⊢ _)               f r⊕⇛
      find′ (._ ⊢> B)         (r⊕⇛ f)    = go (_ ⊢> (_ ⊕> B))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._)  (d⇛⇐ f)    = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find′ ((A <⇛ _) <⊢ ._)  (d⇛⇐ f)    = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find′ (._ ⊢> (A <⇐ _))  (d⇛⇐ f)    = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find′ (._ ⊢> (_ ⇐> B))  (d⇛⇐ f)    = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find′ ((_ ⇛> B) <⊢ ._)  (d⇛⇒ f)    = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find′ ((A <⇛ _) <⊢ ._)  (d⇛⇒ f)    = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find′ (._ ⊢> (_ ⇒> B))  (d⇛⇒ f)    = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find′ (._ ⊢> (A <⇒ _))  (d⇛⇒ f)    = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find′ ((_ ⇚> B) <⊢ ._)  (d⇚⇒ f)    = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find′ ((A <⇚ _) <⊢ ._)  (d⇚⇒ f)    = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find′ (._ ⊢> (_ ⇒> B))  (d⇚⇒ f)    = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find′ (._ ⊢> (A <⇒ _))  (d⇚⇒ f)    = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find′ ((_ ⇚> B) <⊢ ._)  (d⇚⇐ f)    = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find′ ((A <⇚ _) <⊢ ._)  (d⇚⇐ f)    = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (_ ⇐> B))  (d⇚⇐ f)    = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (A <⇐ _))  (d⇚⇐ f)    = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
           → ( I : Contextᴶ - ) (f : LG I [ B ⊗ C ]ᴶ)
           → { J : Contextᴶ - } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
           → Origin′ J (g f)
        go I f {J} g with find′ I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl
\end{code}
\end{hide}
However, there are many cases---53 in total. The reason for this is
that the possible derivation steps depend on the main connective;
therefore we first have to explore every possible main connective, and
then every possible rule which would produce that main connective.
Because of this, the definitions of the various |find′| functions are
very long and tedious, and have mostly been omitted.\footnote{
  The burden on the programmer or logician can be reduced by clever
  use of the symmetries $\cdot^{\bowtie}$ and $\cdot^{\infty}$ as done
  in \citet{moortgat2009}. One would have to implement only
  \textit{three} of the |find′| functions (e.g. for |el|, |⊗| and
  |⇒|); the remaining four can then be derived using the symmetries.
}

From the more general |Origin′| and |find′| we can very easily recover
our original definitions |Origin| and |find| by setting the context
to be empty. In the case of the cut formula |B ⊗ C|, we set the
context to |(_ ⊢> [])| to ensure that the formula ends up at the top
level in the succedent:
\begin{code}
      Origin  : ∀ {A B C} (f : LG A ⊢ B ⊗ C) → Set
      Origin  f = Origin′  (_ ⊢> []) f

      find    : ∀ {A B C} (f : LG A ⊢ B ⊗ C) → Origin f
      find    f = find′    (_ ⊢> []) f
\end{code}
\begin{hide}
\begin{code}
  module ⇒ where

    data Origin′ {B C} (J : Contextᴶ +) (f : LG J [ B ⇒ C ]ᴶ) : Set where
      origin : ∀ {E F}  (h₁  : LG E ⊢ B)
               (h₂  : LG C ⊢ F)
               (f′  : ∀ {G} → LG G ⊢ E ⇒ F → LG J [ G ]ᴶ)
               (pr  : f ≡ f′ (m⇒ h₁ h₂))
                    → Origin′ J f

    mutual
      find′ : ∀ {B C} (J : Contextᴶ +) (f : LG J [ B ⇒ C ]ᴶ) → Origin′ J f
      find′ ([] <⊢ ._)       (m⇒  f g) = origin f g id refl

      find′ ((A <⊗ _) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find′ ((_ ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find′ (._ ⊢> (_ ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find′ (._ ⊢> (A <⇒ _)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find′ (._ ⊢> (_ ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find′ (._ ⊢> (A <⇐ _)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find′ (A <⊢ ._)        (r⊗⇒ f)   = go ((_ ⊗> A) <⊢ _)        f r⊗⇒
      find′ (._ ⊢> (_ ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find′ (._ ⊢> (A <⇒ _)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find′ ((_ ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find′ (._ ⊢> B)        (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> B))        f r⇒⊗
      find′ (A <⊢ ._)        (r⊗⇐ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (_ ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (A <⇐ _)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find′ ((_ ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find′ (._ ⊢> B)        (r⇐⊗ f)   = go (_ ⊢> (B <⇐ _))        f r⇐⊗
      find′ ((A <⇚ _) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find′ ((_ ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find′ ((A <⇛ _) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find′ ((_ ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find′ (._ ⊢> (A <⊕ _)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find′ (._ ⊢> (_ ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find′ (A <⊢ ._)        (r⇚⊕ f)   = go ((A <⇚ _) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find′ ((A <⇚ _) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find′ ((_ ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find′ (._ ⊢> B)        (r⊕⇚ f)   = go (_ ⊢> (B <⊕ _))        f r⊕⇚
      find′ (A <⊢ ._)        (r⇛⊕ f)   = go ((_ ⇛> A) <⊢ _)        f r⇛⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find′ ((A <⇛ _) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find′ (._ ⊢> B)        (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
          → ( I : Contextᴶ + ) (f : LG I [ B ⇒ C ]ᴶ)
          → { J : Contextᴶ + } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin′ J (g f)
        go I f {J} g with find′ I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl

    Origin  : ∀ {A B C} (f : LG A ⇒ B ⊢ C) → Set
    Origin  f = Origin′  ([] <⊢ _) f

    find    : ∀ {A B C} (f : LG A ⇒ B ⊢ C) → Origin f
    find    f = find′    ([] <⊢ _) f
\end{code}
\end{hide}
\begin{hide}
\begin{code}
  module ⇐ where

    data Origin′ {B C} (J : Contextᴶ +) (f : LG J [ B ⇐ C ]ᴶ) : Set where
      origin : ∀ {E F}  (h₁  : LG B ⊢ E)
               (h₂  : LG F ⊢ C)
               (f′  : ∀ {G} → LG G ⊢ E ⇐ F → LG J [ G ]ᴶ)
               (pr  : f ≡ f′ (m⇐ h₁ h₂))
                    → Origin′ J f

    mutual
      find′ : ∀ {B C} (J : Contextᴶ +) (f : LG J [ B ⇐ C ]ᴶ) → Origin′ J f
      find′ ([] <⊢ ._)       (m⇐  f g) = origin f g id refl

      find′ ((A <⊗ _) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find′ ((_ ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find′ (._ ⊢> (_ ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find′ (._ ⊢> (A <⇒ _)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find′ (._ ⊢> (_ ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find′ (._ ⊢> (A <⇐ _)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find′ (A <⊢ ._)        (r⊗⇒ f)   = go ((_ ⊗> A) <⊢ _)        f r⊗⇒
      find′ (._ ⊢> (_ ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find′ (._ ⊢> (A <⇒ _)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find′ ((_ ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find′ (._ ⊢> B)        (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> B))        f r⇒⊗
      find′ (A <⊢ ._)        (r⊗⇐ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (_ ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (A <⇐ _)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find′ ((_ ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find′ (._ ⊢> B)        (r⇐⊗ f)   = go (_ ⊢> (B <⇐ _))        f r⇐⊗
      find′ ((A <⇚ _) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find′ ((_ ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find′ ((A <⇛ _) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find′ ((_ ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find′ (._ ⊢> (A <⊕ _)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find′ (._ ⊢> (_ ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find′ (A <⊢ ._)        (r⇚⊕ f)   = go ((A <⇚ _) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find′ ((A <⇚ _) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find′ ((_ ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find′ (._ ⊢> B)        (r⊕⇚ f)   = go (_ ⊢> (B <⊕ _))        f r⊕⇚
      find′ (A <⊢ ._)        (r⇛⊕ f)   = go ((_ ⇛> A) <⊢ _)        f r⇛⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find′ ((A <⇛ _) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find′ (._ ⊢> B)        (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
          → ( I : Contextᴶ + ) (f : LG I [ B ⇐ C ]ᴶ)
          → { J : Contextᴶ + } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin′ J (g f)
        go I f {J} g with find′ I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl

    Origin  : ∀ {A B C} (f : LG A ⇐ B ⊢ C) → Set
    Origin  f = Origin′  ([] <⊢ _) f

    find    : ∀ {A B C} (f : LG A ⇐ B ⊢ C) → Origin f
    find    f = find′    ([] <⊢ _) f
\end{code}
\end{hide}
\begin{hide}
\begin{code}
  module ⊕ where

    data Origin′ {B C} (J : Contextᴶ +) (f : LG J [ B ⊕ C ]ᴶ) : Set where
      origin : ∀ {E F}  (h₁  : LG B ⊢ E)
               (h₂  : LG C ⊢ F)
               (f′  : ∀ {G} → LG G ⊢ E ⊕ F → LG J [ G ]ᴶ)
               (pr  : f ≡ f′ (m⊕ h₁ h₂))
                    → Origin′ J f
    mutual
      find′ : ∀ {B C} (J : Contextᴶ +) (f : LG J [ B ⊕ C ]ᴶ) → Origin′ J f
      find′ ([] <⊢ ._)       (m⊕  f g) = origin f g id refl

      find′ ((A <⊗ _) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find′ ((_ ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find′ (._ ⊢> (_ ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find′ (._ ⊢> (A <⇒ _)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find′ (._ ⊢> (_ ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find′ (._ ⊢> (A <⇐ _)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find′ (A <⊢ ._)        (r⊗⇒ f)   = go ((_ ⊗> A) <⊢ _)        f r⊗⇒
      find′ (._ ⊢> (_ ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find′ (._ ⊢> (A <⇒ _)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find′ ((_ ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find′ (._ ⊢> B)        (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> B))        f r⇒⊗
      find′ (A <⊢ ._)        (r⊗⇐ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (_ ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (A <⇐ _)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find′ ((_ ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find′ (._ ⊢> B)        (r⇐⊗ f)   = go (_ ⊢> (B <⇐ _))        f r⇐⊗
      find′ ((A <⇚ _) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find′ ((_ ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find′ ((A <⇛ _) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find′ ((_ ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find′ (._ ⊢> (A <⊕ _)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find′ (._ ⊢> (_ ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find′ (A <⊢ ._)        (r⇚⊕ f)   = go ((A <⇚ _) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find′ ((A <⇚ _) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find′ ((_ ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find′ (._ ⊢> B)        (r⊕⇚ f)   = go (_ ⊢> (B <⊕ _))        f r⊕⇚
      find′ (A <⊢ ._)        (r⇛⊕ f)   = go ((_ ⇛> A) <⊢ _)        f r⇛⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find′ ((A <⇛ _) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find′ (._ ⊢> B)        (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
          → ( I : Contextᴶ + ) (f : LG I [ B ⊕ C ]ᴶ)
          → { J : Contextᴶ + } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin′ J (g f)
        go I f {J} g with find′ I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl

    Origin  : ∀ {A B C} (f : LG A ⊕ B ⊢ C) → Set
    Origin  f = Origin′  ([] <⊢ _) f

    find    : ∀ {A B C} (f : LG A ⊕ B ⊢ C) → Origin f
    find    f = find′    ([] <⊢ _) f
\end{code}
\end{hide}
\begin{hide}
\begin{code}
  module ⇚ where

    data Origin′ {B C} (J : Contextᴶ -) (f : LG J [ B ⇚ C ]ᴶ) : Set where
      origin : ∀ {E F}  (h₁  : LG E ⊢ B)
               (h₂  : LG C ⊢ F)
               (f′  : ∀ {G} → LG E ⇚ F ⊢ G → LG J [ G ]ᴶ)
               (pr  : f ≡ f′ (m⇚ h₁ h₂))
                    → Origin′ J f

    mutual
      find′ : ∀ {B C} (J : Contextᴶ -) (f : LG J [ B ⇚ C ]ᴶ) → Origin′ J f
      find′ (._ ⊢> [])       (m⇚  f g) = origin f g id refl

      find′ ((A <⊗ _) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find′ ((_ ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find′ (._ ⊢> (_ ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find′ (._ ⊢> (A <⇒ _)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find′ (._ ⊢> (_ ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find′ (._ ⊢> (A <⇐ _)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find′ (A <⊢ ._)        (r⊗⇒ f)   = go ((_ ⊗> A) <⊢ _)        f r⊗⇒
      find′ (._ ⊢> (_ ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find′ (._ ⊢> (A <⇒ _)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find′ ((_ ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find′ (._ ⊢> B)        (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> B))        f r⇒⊗
      find′ (A <⊢ ._)        (r⊗⇐ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (_ ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (A <⇐ _)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find′ ((_ ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find′ (._ ⊢> B)        (r⇐⊗ f)   = go (_ ⊢> (B <⇐ _))        f r⇐⊗
      find′ ((A <⇚ _) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find′ ((_ ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find′ ((A <⇛ _) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find′ ((_ ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find′ (._ ⊢> (A <⊕ _)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find′ (._ ⊢> (_ ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find′ (A <⊢ ._)        (r⇚⊕ f)   = go ((A <⇚ _) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find′ ((A <⇚ _) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find′ ((_ ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find′ (._ ⊢> B)        (r⊕⇚ f)   = go (_ ⊢> (B <⊕ _))        f r⊕⇚
      find′ (A <⊢ ._)        (r⇛⊕ f)   = go ((_ ⇛> A) <⊢ _)        f r⇛⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find′ ((A <⇛ _) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find′ (._ ⊢> B)        (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
          → ( I : Contextᴶ - ) (f : LG I [ B ⇚ C ]ᴶ)
          → { J : Contextᴶ - } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin′ J (g f)
        go I f {J} g with find′ I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl

    Origin  : ∀ {A B C} (f : LG A ⊢ B ⇚ C) → Set
    Origin  f = Origin′  (_ ⊢> []) f

    find    : ∀ {A B C} (f : LG A ⊢ B ⇚ C) → Origin f
    find    f = find′    (_ ⊢> []) f
\end{code}
\end{hide}
\begin{hide}
\begin{code}
  module ⇛ where

    data Origin′ {B C} (J : Contextᴶ -) (f : LG J [ B ⇛ C ]ᴶ) : Set where
      origin : ∀ {E F}  (h₁   : LG B ⊢ E)
               (h₂   : LG F ⊢ C)
               (f′   : ∀ {G} → LG E ⇛ F ⊢ G → LG J [ G ]ᴶ)
               (pr   : f ≡ f′ (m⇛ h₁ h₂))
                     → Origin′ J f

    mutual
      find′ : ∀ {B C} (J : Contextᴶ -) (f : LG J [ B ⇛ C ]ᴶ) → Origin′ J f
      find′ (._ ⊢> [])       (m⇛  f g) = origin f g id refl

      find′ ((A <⊗ _) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find′ ((_ ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find′ (._ ⊢> (_ ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find′ (._ ⊢> (A <⇒ _)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find′ (._ ⊢> (_ ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find′ (._ ⊢> (A <⇐ _)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find′ (A <⊢ ._)        (r⊗⇒ f)   = go ((_ ⊗> A) <⊢ _)        f r⊗⇒
      find′ (._ ⊢> (_ ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find′ (._ ⊢> (A <⇒ _)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find′ ((_ ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find′ (._ ⊢> B)        (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> B))        f r⇒⊗
      find′ (A <⊢ ._)        (r⊗⇐ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (_ ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (A <⇐ _)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find′ ((_ ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find′ (._ ⊢> B)        (r⇐⊗ f)   = go (_ ⊢> (B <⇐ _))        f r⇐⊗
      find′ ((A <⇚ _) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find′ ((_ ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find′ ((A <⇛ _) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find′ ((_ ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find′ (._ ⊢> (A <⊕ _)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find′ (._ ⊢> (_ ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find′ (A <⊢ ._)        (r⇚⊕ f)   = go ((A <⇚ _) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find′ ((A <⇚ _) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find′ ((_ ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find′ (._ ⊢> B)        (r⊕⇚ f)   = go (_ ⊢> (B <⊕ _))        f r⊕⇚
      find′ (A <⊢ ._)        (r⇛⊕ f)   = go ((_ ⇛> A) <⊢ _)        f r⇛⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find′ ((A <⇛ _) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find′ (._ ⊢> B)        (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
          → ( I : Contextᴶ - ) (f : LG I [ B ⇛ C ]ᴶ)
          → { J : Contextᴶ - } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin′ J (g f)
        go I f {J} g with find′ I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl

    Origin  : ∀ {A B C} (f : LG A ⊢ B ⇛ C) → Set
    Origin  f = Origin′  (_ ⊢> []) f

    find    : ∀ {A B C} (f : LG A ⊢ B ⇛ C) → Origin f
    find    f = find′    (_ ⊢> []) f
\end{code}
\end{hide}
\begin{hide}
\begin{code}
  module el where

    data Origin′ {B} (J : Contextᴶ +) (f : LG J [ el B ]ᴶ) : Set where
      origin :  (f′  : ∀ {G} → LG G ⊢ el B → LG J [ G ]ᴶ)
                (pr  : f ≡ f′ ax)
                     → Origin′ J f

    mutual
      find′ : ∀ {B} (J : Contextᴶ +) (f : LG J [ el B ]ᴶ) → Origin′ J f
      find′ ([] <⊢ ._)       ax        = origin id refl

      find′ ((A <⊗ _) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find′ ((_ ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find′ (._ ⊢> (_ ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find′ (._ ⊢> (A <⇒ _)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find′ (._ ⊢> (_ ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find′ (._ ⊢> (A <⇐ _)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find′ (A <⊢ ._)        (r⊗⇒ f)   = go ((_ ⊗> A) <⊢ _)        f r⊗⇒
      find′ (._ ⊢> (_ ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find′ (._ ⊢> (A <⇒ _)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find′ ((_ ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find′ (._ ⊢> B)        (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> B))        f r⇒⊗
      find′ (A <⊢ ._)        (r⊗⇐ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (_ ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find′ (._ ⊢> (A <⇐ _)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find′ ((_ ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find′ ((A <⊗ _) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find′ (._ ⊢> B)        (r⇐⊗ f)   = go (_ ⊢> (B <⇐ _))        f r⇐⊗
      find′ ((A <⇚ _) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find′ ((_ ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find′ ((A <⇛ _) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find′ ((_ ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find′ (._ ⊢> (A <⊕ _)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find′ (._ ⊢> (_ ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find′ (A <⊢ ._)        (r⇚⊕ f)   = go ((A <⇚ _) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find′ ((A <⇚ _) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find′ ((_ ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find′ (._ ⊢> B)        (r⊕⇚ f)   = go (_ ⊢> (B <⊕ _))        f r⊕⇚
      find′ (A <⊢ ._)        (r⇛⊕ f)   = go ((_ ⇛> A) <⊢ _)        f r⇛⊕
      find′ (._ ⊢> (_ ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find′ (._ ⊢> (A <⊕ _)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find′ ((A <⇛ _) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find′ (._ ⊢> B)        (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇛
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find′ ((_ ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find′ ((A <⇛ _) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find′ (._ ⊢> (_ ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find′ (._ ⊢> (A <⇒ _)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find′ ((_ ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find′ ((A <⇚ _) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (_ ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find′ (._ ⊢> (A <⇐ _)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B}
          → ( I : Contextᴶ + ) (f : LG I [ el B ]ᴶ)
          → { J : Contextᴶ + } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin′ J (g f)
        go I x {J} g with find′ I x
        ... | origin f pr rewrite pr = origin (g ∘ f) refl

    Origin  : ∀ {A B} (f : LG el A ⊢ B) → Set
    Origin  f = Origin′  ([] <⊢ _) f

    find    : ∀ {A B} (f : LG el A ⊢ B) → Origin f
    find    f = find′    ([] <⊢ _) f
\end{code}
\end{hide}
And with that, we can finally put the rewrite rules from
\citet{moortgat1999} to use. We can define |cut′| by pattern
matching on the cut formula |B|; applying the appropriate |find′|
function to find′ the monotonicity rule introducing the formula; and
apply the appropriate rewrite rule to create a derivation containing
two cuts on structurally smaller formulas:
\begin{code}
  cut′ : ∀ {A B C} (f : LG A ⊢ B) (g : LG B ⊢ C) → LG A ⊢ C

  cut′ {B = el _ }  f  g with el.find g
  ...  | (el.origin        g′ _)  = g′ f

  cut′ {B = _ ⊗ _}  f  g with ⊗.find f
  ...  | (⊗.origin  h₁ h₂  f′ _)  = f′ (r⇐⊗ (cut′ h₁ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ g))))))

  cut′ {B = _ ⇐ _}  f  g with ⇐.find g
  ...  | (⇐.origin  h₁ h₂  g′ _)  = g′ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ (cut′ (r⇐⊗ f) h₁)))))

  cut′ {B = _ ⇒ _}  f  g with ⇒.find g
  ...  | (⇒.origin  h₁ h₂  g′ _)  = g′ (r⊗⇒ (r⇐⊗ (cut′ h₁ (r⊗⇐ (cut′ (r⇒⊗ f) h₂)))))

  cut′ {B = _ ⊕ _}  f  g with ⊕.find g
  ...  | (⊕.origin  h₁ h₂  g′ _)  = g′ (r⇚⊕ (cut′ (r⊕⇚ (r⇛⊕ (cut′ (r⊕⇛ f) h₂))) h₁))

  cut′ {B = _ ⇚ _}  f  g with ⇚.find f
  ...  | (⇚.origin  h₁ h₂  f′ _)  = f′ (r⊕⇚ (r⇛⊕ (cut′ (r⊕⇛ (cut′ h₁ (r⇚⊕ g))) h₂)))

  cut′ {B = _ ⇛ _}  f  g with ⇛.find f
  ...  | (⇛.origin  h₁ h₂  f′ _)  = f′ (r⊕⇛ (r⇚⊕ (cut′ (r⊕⇚ (cut′ h₂ (r⇛⊕ g))) h₁)))
\end{code}



\section{CPS Translation}

For this paper, we have opted to implement the call-by-value CPS
translation as described in \citet{moortgat2007}. This translation
consists of three elements:
\begin{itemize}
\item%
  a function |⌈_⌉|, which translates formulas in LG to formulas in the
  target system---while we have chosen to translate to Agda, the
  original translation targeted multiplicative intuitionistic linear
  logic;
\item%
  a pair of mutually recursive functions |⌈_⌉ᴸ| and |⌈_⌉ᴿ|, which
  translate terms in LG to terms in the target system.
\end{itemize}
In order to write these functions, we will need two additional pieces
of information: a function |⌈_⌉ᴬ|, which translates the atomic
formulas to Agda types; and a return type |R|, which we will use to
define a ``negation'' as |¬ A = A → R|. We will therefore implement
the CPS translation in a sub-module, which abstracts over these terms:
\begin{code}
  module translation (⌈_⌉ᴬ : Atom → Set) (R : Set) where
\end{code}
\begin{hide}
\begin{code}
    infixr 9 ¬_
\end{code}
\end{hide}
When using this module, we will generally identify the return type
|R| with the type |Bool| for booleans. However, abstracting over it
will ensure that we do not accidentally use this knowledge during the
translation.
\begin{hide}
\begin{code}
    ¬_ : Set → Set
    ¬ A = A → R
\end{code}
\end{hide}

The type-level translation itself maps formulas in LG to types in
Agda, as follows:
\begin{code}
    ⌈_⌉ : Type → Set
    ⌈ el   A  ⌉ =        ⌈ A ⌉ᴬ
    ⌈ A ⊗  B  ⌉ =    (   ⌈ A ⌉ ×    ⌈ B ⌉)
    ⌈ A ⇒  B  ⌉ = ¬  (   ⌈ A ⌉ × ¬  ⌈ B ⌉)
    ⌈ B ⇐  A  ⌉ = ¬  (¬  ⌈ B ⌉ ×    ⌈ A ⌉)
    ⌈ B ⊕  A  ⌉ = ¬  (¬  ⌈ B ⌉ × ¬  ⌈ A ⌉)
    ⌈ B ⇚  A  ⌉ =    (   ⌈ B ⌉ × ¬  ⌈ A ⌉)
    ⌈ A ⇛  B  ⌉ =    (¬  ⌈ A ⌉ ×    ⌈ B ⌉)
\end{code}
\begin{hide}
\begin{code}
    deMorgan : {A B : Set} → (¬ ¬ A) → (¬ ¬ B) → ¬ ¬ (A × B)
    deMorgan c₁ c₂ k = c₁ (λ x → c₂ (λ y → k (x , y)))
\end{code}
\end{hide}
The translations on terms map terms in LG to the Agda function
space. Each LG term is associated with \textit{two} functions,
depending on whether the focus is on $A$ or $B$ as the active formula:
\setboolean{partial}{true}%
\begin{code}
    mutual
      ⌈_⌉ᴸ : ∀ {A B} → LG A ⊢ B → ¬ ⌈ B ⌉ → ¬ ⌈ A ⌉
      ⌈_⌉ᴿ : ∀ {A B} → LG A ⊢ B → ⌈ A ⌉ → ¬ ¬ ⌈ B ⌉
\end{code}
\setboolean{partial}{false}%
The CPS translations of the terms are rather verbose, and trivial to
deduce, when guided by the translation on types. Therefore, in the
interest of space they have been omitted from the paper.\footnote{
  They are, however, present in the source and therefore available on
  GitHub.
}
\begin{hide}
\begin{code}
      ⌈ ax       ⌉ᴸ k x  = k x
      ⌈ r⇒⊗ f    ⌉ᴸ   x  =    λ{(y , z) → ⌈ f ⌉ᴸ (λ k → k (y , x)) z}
      ⌈ r⊗⇒ f    ⌉ᴸ k x  = k (λ{(y , z) → ⌈ f ⌉ᴸ z (y , x)})
      ⌈ r⇐⊗ f    ⌉ᴸ   x  =    λ{(y , z) → ⌈ f ⌉ᴸ (λ k → k (x , z)) y}
      ⌈ r⊗⇐ f    ⌉ᴸ k x  = k (λ{(y , z) → ⌈ f ⌉ᴸ y (x , z)})
      ⌈ m⊗  f g  ⌉ᴸ k    =    λ{(x , y) → deMorgan (⌈ f ⌉ᴿ x) (⌈ g ⌉ᴿ y) k}
      ⌈ m⇒  f g  ⌉ᴸ k k′ = k (λ{(x , y) → deMorgan (⌈ f ⌉ᴿ x) (λ k → k  (⌈ g ⌉ᴸ y)) k′})
      ⌈ m⇐  f g  ⌉ᴸ k k′ = k (λ{(x , y) → deMorgan (λ k → k  (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k′})
      ⌈ r⇛⊕ f    ⌉ᴸ k x  = k (λ{(y , z) → ⌈ f ⌉ᴸ z (y , x)})
      ⌈ r⊕⇛ f    ⌉ᴸ   x  =    λ{(y , z) → ⌈ f ⌉ᴸ (λ k → k (y , x)) z}
      ⌈ r⇚⊕ f    ⌉ᴸ k x  = k (λ{(y , z) → ⌈ f ⌉ᴸ y (x , z)})
      ⌈ r⊕⇚ f    ⌉ᴸ   x  =    λ{(y , z) → ⌈ f ⌉ᴸ (λ k → k (x , z)) y}
      ⌈ m⊕  f g  ⌉ᴸ k k′ = k (λ{(x , y) → k′ (⌈ f ⌉ᴸ x , ⌈ g ⌉ᴸ y)})
      ⌈ m⇛  f g  ⌉ᴸ k    =    λ{(x , y) → deMorgan (λ k → k (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k}
      ⌈ m⇚  f g  ⌉ᴸ k    =    λ{(x , y) → deMorgan (⌈ f ⌉ᴿ x) (λ k → k (⌈ g ⌉ᴸ y)) k}
      ⌈ d⇛⇐ f    ⌉ᴸ k    =    λ{(x , y) → k (λ{(z , w) → ⌈ f ⌉ᴸ (λ k → k (x , z)) (y , w)})}
      ⌈ d⇛⇒ f    ⌉ᴸ k    =    λ{(x , y) → k (λ{(z , w) → ⌈ f ⌉ᴸ (λ k → k (x , w)) (z , y)})}
      ⌈ d⇚⇒ f    ⌉ᴸ k    =    λ{(x , y) → k (λ{(z , w) → ⌈ f ⌉ᴸ (λ k → k (w , y)) (z , x)})}
      ⌈ d⇚⇐ f    ⌉ᴸ k    =    λ{(x , y) → k (λ{(z , w) → ⌈ f ⌉ᴸ (λ k → k (z , y)) (x , w)})}

      ⌈ ax       ⌉ᴿ  x      k  = k x
      ⌈ r⇒⊗ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ y (λ k → k (x , z))
      ⌈ r⊗⇒ f    ⌉ᴿ  x      k  = k (λ{(y , z) → ⌈ f ⌉ᴿ (y , x) z})
      ⌈ r⇐⊗ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ x (λ k → k (z , y))
      ⌈ r⊗⇐ f    ⌉ᴿ  x      k  = k (λ{(y , z) → ⌈ f ⌉ᴿ (x , z) y})
      ⌈ m⊗  f g  ⌉ᴿ (x , y) k  = deMorgan (⌈ f ⌉ᴿ x) (⌈ g ⌉ᴿ y) k
      ⌈ m⇒  f g  ⌉ᴿ  k′     k  = k (λ{(x , y) → deMorgan (⌈ f ⌉ᴿ x) (λ k → k (⌈ g ⌉ᴸ y)) k′})
      ⌈ m⇐  f g  ⌉ᴿ  k′     k  = k (λ{(x , y) → deMorgan (λ k → k (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k′})
      ⌈ r⇛⊕ f    ⌉ᴿ  x      k  = k (λ{(y , z) → ⌈ f ⌉ᴿ (y , x) z})
      ⌈ r⊕⇛ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ y (λ k → k (x , z))
      ⌈ r⊕⇚ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ x (λ k → k (z , y))
      ⌈ r⇚⊕ f    ⌉ᴿ  x      k  = k (λ{(y , z) → ⌈ f ⌉ᴿ (x , z) y})
      ⌈ m⊕  f g  ⌉ᴿ  k′     k  = k (λ{(x , y) → k′ (⌈ f ⌉ᴸ x , ⌈ g ⌉ᴸ y)})
      ⌈ m⇛  f g  ⌉ᴿ (x , y) k  = deMorgan (λ k → k (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k
      ⌈ m⇚  f g  ⌉ᴿ (x , y) k  = deMorgan (⌈ f ⌉ᴿ x) (λ k → k (⌈ g ⌉ᴸ y)) k
      ⌈ d⇛⇐ f    ⌉ᴿ (x , y) k  = k (λ{(z , w) → ⌈ f ⌉ᴿ (y , w) (λ k → k (x , z))})
      ⌈ d⇛⇒ f    ⌉ᴿ (x , y) k  = k (λ{(z , w) → ⌈ f ⌉ᴿ (z , y) (λ k → k (x , w))})
      ⌈ d⇚⇒ f    ⌉ᴿ (x , y) k  = k (λ{(z , w) → ⌈ f ⌉ᴿ (z , x) (λ k → k (w , y))})
      ⌈ d⇚⇐ f    ⌉ᴿ (x , y) k  = k (λ{(z , w) → ⌈ f ⌉ᴿ (x , w) (λ k → k (z , y))})
\end{code}
\end{hide}



\section{Example}

In this final section, we will present the analysis of an example
sentence, using the type-logical grammar implemented above. The
example we will analyse is:
\begin{quote}
``Someone loves everyone.''
\end{quote}
This sentence is well known to be ambiguous, owing to the presence of
the two quantifiers. There are two readings:
\begin{enumerate}
\item[a.] There is some person who loves every person.
\item[b.] For each person, there is some person who loves them.
\end{enumerate}
We will demonstrate that the system, as implemented in this paper,
accurately captures these readings.

Before we can do that, however, there is a small amount of boiler
plate that we have to deal with: we still need to choose a
representation for our atomic types, and show how these translate into
Agda.
\begin{hide}
\begin{code}
module example where
\end{code}
\end{hide}
In what follows, we will assume we have access to a type for entities,
suitable definitions for the universal and existential quantifiers,
and meanings for `loves' and `person':
\begin{code}
  postulate
    Entity  : Set
    forAll  : (Entity → Bool) → Bool
    exists  : (Entity → Bool) → Bool
    ʟᴏᴠᴇs   : Entity → Entity → Bool
    ᴘᴇʀsᴏɴ  : Entity → Bool
\end{code}
\begin{hide}
\begin{code}
    _⊃_     : Bool → Bool → Bool
\end{code}
\end{hide}
We will instantiate the type for atomic formulas to |Atom|, as defined
below:
\begin{code}
  data Atom : Set where N NP S : Atom
\end{code}
Last, we need to define a function which maps the values of |Atom| to
Agda types. We would like to map the atomic formulas as follows:
\begin{code}
  ⌈_⌉ᴬ : Atom → Set
  ⌈ N   ⌉ᴬ = Entity → Bool
  ⌈ NP  ⌉ᴬ = Entity
  ⌈ S   ⌉ᴬ = Bool
\end{code}
Now that we have |Atom| and |⌈_⌉ᴬ|, we can open up the modules defined
as above, instantiating the return type |R| with the type of booleans.
\begin{code}
  open logic              Atom
  open logic.translation  Atom ⌈_⌉ᴬ Bool
\end{code}
\begin{hide}
\begin{code}
  n np s : Type
  n   = el N
  np  = el NP
  s   = el S
\end{code}
\end{hide}
With everything that we implemented in scope, we can now define a
small lexicon for our example sentence.

In what follows, we will use the aliases |n|, |np| and |s| for |el N|,
|el NP| and |el S|, respectively:
\begin{code}
  someone   : ⌈ (np ⇐ n) ⊗ n ⌉
  someone   = ((λ{(g , f) → exists (λ x → f x ∧ g x)}) , ᴘᴇʀsᴏɴ)

  loves     : ⌈ (np ⇒ s) ⇐ np ⌉
  loves     = λ{(k , y) → k (λ{(x , k) → k (ʟᴏᴠᴇs x y)})}

  everyone  : ⌈ (np ⇐ n) ⊗ n ⌉
  everyone  = ((λ{(g , f) → forAll (λ x → f x ⊃ g x)}) , ᴘᴇʀsᴏɴ)
\end{code}
Given the types we used for our lexical entries, the judgement which
asserts the grammaticality of our sentence becomes:
\begin{hide}
\begin{code}
  sᴇɴᴛ₀ sᴇɴᴛ₁ sᴇɴᴛ₂ sᴇɴᴛ₃ sᴇɴᴛ₄ sᴇɴᴛ₅ sᴇɴᴛ₆ : LG
\end{code}
\end{hide}
\begin{code}
    ( ( np ⇐ n ) ⊗ n ) ⊗ ( ( ( np ⇒ s ) ⇐ np ) ⊗ ( ( np ⇐ n ) ⊗ n ) ) ⊢ s
\end{code}
There are seven proofs of this judgement. Below we have
included the first \textit{two} proofs:\footnote{
  We have chosen not to include the other five proofs as, under the
  CPS translation, they have the same interpretations as either the
  first or the second proof.
  For the interested reader, however, the proofs are present in the
  source, and therefore available on GitHub.
}:
\setboolean{partial}{true}%
\begin{hide}
\begin{code}
  open import Data.Bool                  using (Bool; true; false)
  open import Data.Empty                 using (⊥)
  open import Data.List                  using (List; _∷_; [])
  open import Data.String                using (String; _++_)
  open import Data.Unit                  using (⊤)
  open import Relation.Nullary.Decidable using (⌊_⌋)
  open import Reflection

  mutual
    dropAbs : Term → Term
    dropAbs (var x args)                                = var x (dropAbsArgs args)
    dropAbs (con c args)                                = con c (dropAbsArgs args)
    dropAbs (def f args)                                = def f (dropAbsArgs args)
    dropAbs (lam v (abs _ x))                           = lam v (abs "_" (dropAbs x))
    dropAbs (pi (arg i (el s₁ t₁)) (abs _ (el s₂ t₂)))  = pi (arg i (el s₁ (dropAbs t₁))) (abs "_" (el s₂ (dropAbs t₂)))
    dropAbs t = t

    dropAbsArgs : List (Arg Term) → List (Arg Term)
    dropAbsArgs []               = []
    dropAbsArgs (arg i x ∷ args) = arg i (dropAbs x) ∷ dropAbsArgs args

  assert : Bool → Term
  assert true  = def (quote ⊤) []
  assert false = def (quote ⊥) []

  infix 0 _↦_

  macro
    _↦_ : Term → Term → Term
    act ↦ exp = assert ⌊ dropAbs act ≟ dropAbs exp ⌋
\end{code}
\end{hide}
\begin{code}
  sᴇɴᴛ₀  = r⇒⊗ (r⇐⊗ (m⇐ (m⇒ (r⇐⊗ ax′) ax) (r⇐⊗ ax′)))
  sᴇɴᴛ₁  = r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (r⇐⊗ (m⇐ ax′ (r⇐⊗ ax′))))) ax))
\end{code}
\setboolean{partial}{false}%
\begin{hide}
\begin{code}
  sᴇɴᴛ₂  = r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ (r⇐⊗ ax′) ax) ax))) ax)))
  sᴇɴᴛ₃  = r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ ax′)) ax))))) ax))
  sᴇɴᴛ₄  = r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ ax′)) ax)))) (r⇐⊗ ax′)))
  sᴇɴᴛ₅  = r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ ax′)) ax)))) ax))) ax)))
  sᴇɴᴛ₆  = r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (r⇐⊗ ax′))) ax))))) ax)))
\end{code}
\end{hide}
We can now apply our CPS translation to compute the denotations of our
sentence, passing in the denotations of the words as a tuple, and
passing in the identity function as the last argument in order to
obtain the result:
\begin{hide}
\begin{code}
\end{code}
\end{hide}
\setboolean{partial}{true}%
\begin{code}
  sent₀  : ⌈ sᴇɴᴛ₀ ⌉ᴿ (someone , loves , everyone) id  ↦  forAll (λ y → ᴘᴇʀsᴏɴ y ⊃ exists (λ x → ᴘᴇʀsᴏɴ x ∧ ʟᴏᴠᴇs x y))
  sent₁  : ⌈ sᴇɴᴛ₁ ⌉ᴿ (someone , loves , everyone) id  ↦  exists (λ x → ᴘᴇʀsᴏɴ x ∧ forAll (λ y → ᴘᴇʀsᴏɴ y ⊃ ʟᴏᴠᴇs x y))
\end{code}
\setboolean{partial}{false}%
\begin{hide}
\begin{code}
  sent₂  : ⌈ sᴇɴᴛ₂ ⌉ᴿ (someone , loves , everyone) id  ↦  forAll (λ y → ᴘᴇʀsᴏɴ y ⊃ exists (λ x → ᴘᴇʀsᴏɴ x ∧ ʟᴏᴠᴇs x y))
  sent₃  : ⌈ sᴇɴᴛ₃ ⌉ᴿ (someone , loves , everyone) id  ↦  exists (λ x → ᴘᴇʀsᴏɴ x ∧ forAll (λ y → ᴘᴇʀsᴏɴ y ⊃ ʟᴏᴠᴇs x y))
  sent₄  : ⌈ sᴇɴᴛ₄ ⌉ᴿ (someone , loves , everyone) id  ↦  forAll (λ y → ᴘᴇʀsᴏɴ y ⊃ exists (λ x → ᴘᴇʀsᴏɴ x ∧ ʟᴏᴠᴇs x y))
  sent₅  : ⌈ sᴇɴᴛ₅ ⌉ᴿ (someone , loves , everyone) id  ↦  forAll (λ y → ᴘᴇʀsᴏɴ y ⊃ exists (λ x → ᴘᴇʀsᴏɴ x ∧ ʟᴏᴠᴇs x y))
  sent₆  : ⌈ sᴇɴᴛ₆ ⌉ᴿ (someone , loves , everyone) id  ↦  forAll (λ y → ᴘᴇʀsᴏɴ y ⊃ exists (λ x → ᴘᴇʀsᴏɴ x ∧ ʟᴏᴠᴇs x y))
\end{code}
\end{hide}
\begin{hide}
\begin{code}
  sent₀  = _
  sent₁  = _
  sent₂  = _
  sent₃  = _
  sent₄  = _
  sent₅  = _
  sent₆  = _
\end{code}
\end{hide}
\textit{Voila}! Our system produces exactly the expected readings.

\begin{figure*}[ht]
\centering
\begin{minipage}[b]{0.495\textwidth}%
\centering%
\begin{scprooftree}{0.85}%
\RightLabel{\tiny{$(\text{ax})$}}%
\AXC{$np \fCenter np$}%
\RightLabel{\tiny{$(\text{ax})$}}%
\AXC{$n \fCenter n$}%
\RightLabel{\tiny{$(m\varslash)$}}%
\BIC{$np \varslash n \fCenter np \varslash n$}%
\RightLabel{\tiny{$(r\varslash\varotimes)$}}%
\UIC{$(np \varslash n) \varotimes n \fCenter np$}%
\RightLabel{\tiny{$(\text{ax})$}}%
\AXC{$s \fCenter s$}%
\RightLabel{\tiny{$(m\varbslash)$}}%
\BIC{$np \varbslash s \fCenter (np \varslash n) \varotimes n \varbslash s$}%
\RightLabel{\tiny{$(\text{ax})$}}%
\AXC{$np \fCenter np$}%
\RightLabel{\tiny{$(\text{ax})$}}%
\AXC{$n \fCenter n$}%
\RightLabel{\tiny{$(m\varslash)$}}%
\BIC{$np \varslash n \fCenter np \varslash n$}%
\RightLabel{\tiny{$(r\varslash\varotimes)$}}%
\UIC{$(np \varslash n) \varotimes n \fCenter np$}%
\RightLabel{\tiny{$(m\varslash)$}}%
\BIC{$(np \varbslash s) \varslash np \fCenter ((np \varslash n) \varotimes n \varbslash s) \varslash (np \varslash n) \varotimes n$}%
\RightLabel{\tiny{$(r\varslash\varotimes)$}}%
\UIC{$((np \varbslash s) \varslash np) \varotimes (np \varslash n) \varotimes n \fCenter (np \varslash n) \varotimes n \varbslash s$}%
\RightLabel{\tiny{$(r\varbslash\varotimes)$}}%
\UIC{$((np \varslash n) \varotimes n) \varotimes ((np \varbslash s) \varslash np) \varotimes (np \varslash n) \varotimes n \fCenter s$}%
\end{scprooftree}%
$\forall\,(\lambda y\,→\,\textsc{person}\,y\,\supset\,\exists\,(\lambda x\,→\,\textsc{person}\,x\,\land\,\textsc{loves}\,x\,y))$%
\end{minipage}%
\begin{minipage}[b]{0.495\textwidth}%
\centering%
\begin{scprooftree}{0.85}%
\RightLabel{\tiny{$(\text{ax})$}}%
\AXC{$np \fCenter np$}%
\RightLabel{\tiny{$(\text{ax})$}}%
\AXC{$s \fCenter s$}%
\RightLabel{\tiny{$(m\varbslash)$}}%
\BIC{$np \varbslash s \fCenter np \varbslash s$}%
\RightLabel{\tiny{$(\text{ax})$}}%
\AXC{$np \fCenter np$}%
\RightLabel{\tiny{$(\text{ax})$}}%
\AXC{$n \fCenter n$}%
\RightLabel{\tiny{$(m\varslash)$}}%
\BIC{$np \varslash n \fCenter np \varslash n$}%
\RightLabel{\tiny{$(r\varslash\varotimes)$}}%
\UIC{$(np \varslash n) \varotimes n \fCenter np$}%
\RightLabel{\tiny{$(m\varslash)$}}%
\BIC{$(np \varbslash s) \varslash np \fCenter (np \varbslash s) \varslash (np \varslash n) \varotimes n$}%
\RightLabel{\tiny{$(r\varslash\varotimes)$}}%
\UIC{$((np \varbslash s) \varslash np) \varotimes (np \varslash n) \varotimes n \fCenter np \varbslash s$}%
\RightLabel{\tiny{$(r\varbslash\varotimes)$}}%
\UIC{$np \varotimes ((np \varbslash s) \varslash np) \varotimes (np \varslash n) \varotimes n \fCenter s$}%
\RightLabel{\tiny{$(r\varotimes\varslash)$}}%
\UIC{$np \fCenter s \varslash ((np \varbslash s) \varslash np) \varotimes (np \varslash n) \varotimes n$}%
\RightLabel{\tiny{$(\text{ax})$}}%
\AXC{$n \fCenter n$}%
\RightLabel{\tiny{$(m\varslash)$}}%
\BIC{$np \varslash n \fCenter (s \varslash ((np \varbslash s) \varslash np) \varotimes (np \varslash n) \varotimes n) \varslash n$}%
\RightLabel{\tiny{$(r\varslash\varotimes)$}}%
\UIC{$(np \varslash n) \varotimes n \fCenter s \varslash ((np \varbslash s) \varslash np) \varotimes (np \varslash n) \varotimes n$}%
\RightLabel{\tiny{$(r\varslash\varotimes)$}}%
\UIC{$((np \varslash n) \varotimes n) \varotimes ((np \varbslash s) \varslash np) \varotimes (np \varslash n) \varotimes n \fCenter s$}%
\end{scprooftree}%
$\exists\,(\lambda x\,\to\,\textsc{person}\,x\,\land\,\forall\,(\lambda y\,\to\,\textsc{person}\,y\,\supset\,\textsc{loves}\,x\,y))$%
\end{minipage}%
\caption{``Someone loves everyone.''}\label{someone_loves_everyone}%
\end{figure*}


\section{Conclusion}
We have presented the reader with a simple formalisation of the
Lambek-Grishin calculus, using the proof assistant Agda. We have shown
how to formalise the proof of the admissibility of cut from
\citet{moortgat1999} in Agda, and have extended this proof to cover
all of LG. While we have not covered any of the usual unary operators,
the formalism presented here generalises straightforwardly to
accommodate connectives of any arity---and this extension, together
with many other extensions, are indeed implemented in the full version
of our code.

We have then presented the reader with a call-by-value CPS
translation into the host language Agda, and used this translation to
demonstrate the analysis of an example sentence.

Most importantly, we hope we presented the reader with a clean and
readable formalisation of the Lambek-Grishin calculus.

\section{Related \& Future Work}
Previous work on the formalisation of Lambek calculi was done in Coq
by \citet{anoun2004}, who, amongst other things, implemented sequent
calculus and natural deduction systems for multi-modal categorial
grammars.

The work presented in this paper is part of a larger undertaking to
formalise type-logical grammars in Agda. At the moment, we have
formalised not only the algebraic Lambek-Grishin calculus---which was
presented in this paper---but also structural and polarised varieties
of this calculus. From these implementations, we are able to extract
implementations of their respective non-associative Lambek calculi.

In addition, we have implemented various other multi-modal systems,
such as $\text{NL}_{\textit{CL}}$~\citep{bs2015}.

We aim to extend this work by further formalising the known work
w.r.t.\ these calculi, and creating tools to accommodate the writing
of formal linguistics papers in literate style.

\nocite{*}
\bibliographystyle{apalike}
\bibliography{main}

\end{document}
