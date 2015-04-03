\documentclass{llncs}

%include main.fmt
\include{preamble}

\begin{document}

\title{Formalising type-logical grammars in Agda}%
\author{Pepijn Kokke}%
\institute{Utrecht University}%
\maketitle

\begin{abstract}
In recent years, the interest in using proof assistants to reason about
categorial grammars has grown. The advantage of using proof assistants
is that they allow one to write formally verified proofs about one's
logical systems. The downside is that in many cases the formal proofs
are written as an afterthought, are incomplete, or use obtuse
syntax. This makes it that the verified proofs are often much more
difficult to read than the pen-and-paper proofs, and almost never
directly published.

In this paper, we will try to remedy that by example. Concretely, we
use Agda to model the Lambek-Grishin calculus, a grammar logic with a
rich vocabulary of type-forming operations. We present a verified
procedure for cut elimination in this system.
\end{abstract}


\begin{hide}
\begin{code}
open import Function using (id; flip; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}
\end{hide}


\section{Introduction}

Why would we want to formalise categorial grammars using proof
assistants? One good reason is that it allows us to write formally
verified proofs about the theoretical properties of our categorial
grammars. But not only that---it allows us to directly run our proofs
as programs. For instance, we can directly run the procedure for cut
elimination in this paper to investigate what kind of derivations are
created by it \textit{and} be confident in its correctness.

Why, then, would we want to use Agda instead of more a established
proof assistant such as, for instance, Coq? There are several good
reasons, but we believe that the syntactic freedom offered by Agda is
the most important.
It is this freedom that allows us to write machine-checkable proofs,
formatted in a way which very closely resembles the way one would
otherwise typeset those proofs---a way which is highly readable,
directly publishable, yet still machine-checkable.
This means that we can be confident that the proofs as they are
published are correct, and that they are necessarily complete---for
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

We will formalise the Lambek-Grishin calculus in Agda, and present a
verified procedure for cut elimination in this system.

Since this paper is by no means a complete introduction to Agda or to
dependently-typed programming, we advise the interested reader to
refer to \citet{norell2009} for a detailed discussion of Agda.

It should be mentioned that (although we omit some of the more tedious
parts) this paper is written in literate Agda, and the code has been
made available on GitHub.\footnote{
  See \url{https://gist.github.com/anonymous/02dfa69d41a63d80f0fe}.
}


\section{Formulas, Judgements, Base System}

If we want to model our categorial grammars in Agda, a natural
starting point would be our atomic formulas---such as |n|, |np|, |s|,
etc. These could easily be represented as an enumerated data
type. However, in order to avoid committing to a certain set of atomic
formulas, and side-step the debate on which formulas \textit{should} be
atomic, we will simply assume there is a some data type representing
our atomic formulas:
\begin{code}
module main (Univ : Set) where
\end{code}
Our formulas can easily be described as a data type, injecting our
atomic formulas by means of the constructor |el|, and adding the
familiar connectives from the Lambek-Grishin calculus as binary
constructors. Note that, in Agda, we can use underscores in
definitions to denote argument positions. This means that |_⊗_| below
defines an infix, binary connective:
\begin{code}
data Type : Set where
  el           : Univ  → Type
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
infix   1   LG_
infixr  20  _⇒_
infixl  20  _⇐_
infixl  25  _⇚_
infixr  25  _⇛_
infixr  30  _⊗_
infixr  30  _⊕_
\end{code}
\end{hide}
Next we will define a data type to represent our logical system. This
is where we can use the dependent type system to our advantage. The
constructors for our data type will represent the axiomatic inference
rules of the system, and their \textit{types} will be constrained by
judgements. Below you can see the entire system \textit{LG} as an Agda
data type\footnote{
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
Note that Agda allows any unicode character in identifiers, so |r⊗⇒|
is a valid Agda identifier.

Using this data type, we can already do quite a lot. For instance, we
can show that while the inference rule |ax| above is restricted to
atomic formulas, the unrestricted version is admissible, by induction on
the formula. Note that the construction |{A = ...}| below is used to
pattern match on an implicit variable |A|:
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
chosen, using residuation and monotonicity rules, is that transitivity
becomes an admissible rule.




\section{Admissible Transitivity}

We would like to show that |trans′| of type |LG A ⊢ B → LG B ⊢ C → LG A ⊢ C| is
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
  based on its main connective;
\item\label{p4} due to~\ref{p1} and~\ref{p3}, when we find such an
  immutable formula, we can be sure that, stepping through the
  derivation, after some number of steps we will find the monotonicity
  rule which introduced that formula;
\item\label{p5} due to the type of |trans′|, when we match on the cut
  formula |B| we will always have an immutable variant of that formula
  in either the first or the second argument of |trans′|;
\item\label{p6} finally, for each main connective there exists a
  rewrite rule which makes use of the facts in~\ref{p4} and~\ref{p5}
  to rewrite an application of |trans′| to a derivation with two
  smaller applications of |trans′| on the arguments of the main
  connective in |B| (for binary connectives), or simply to a dervation
  (for atomic formulas). As an example, the rewrite rule for |_⊗_|
  can be found in figure~\ref{cut:otimes}.
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
need two derivations |h₁| and |h₂|, and a derivation |f′| which
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
induction on the given derivation:
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
residuation; and b) when fully taken apart, will leave the nested
formula on the correct side of the turnstile. A natural fit for this
is using Spolarity:
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
been mostly omitted:
\begin{spec}
_[_] : Context p₁ p₂ → Type → Type
[]        [ A ] = A
(B ⊗> C)  [ A ] = B ⊗ (C [ A ])
...
\end{spec}
\begin{hide}
\begin{code}
_[_] : ∀ {p₁ p₂} → Context p₁ p₂ → Type → Type
[]        [ A ] = A
(B ⊗> C)  [ A ] = B ⊗ (C [ A ])
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
\begin{spec}
  data Origin′ (J   : Contextᴶ -)
               (f   : LG J [ B ⊗ C ]ᴶ)
                    : Set where

    origin :   (h₁  : LG E ⊢ B)
               (h₂  : LG F ⊢ C)
               (f′  : ∀ {G} → LG E ⊗ F ⊢ G → LG J [ G ]ᴶ)
               (pr  : f ≡ f′ (m⊗ h₁ h₂))
                    → Origin′ J⁻ f
\end{spec}
Using this more general definition |Origin′|, we can define a more general
function |find′|---and this time, our proof by induction works!

Note that in Agda, the |with| construct is used to pattern match on
the result of an expression:
\begin{spec}
  find′ : (J : Contextᴶ -) (f : LG J [ B ⊗ C ]ᴶ) → Origin′ J f
  find′ (_ ⊢> []) (m⊗   f g  )   = origin f g id refl
  find′ (_ ⊢> []) (r⇒⊗  f    )   with find′ (_ ⊢> (_ ⇒> [])) f
  ... | (origin h₁ h₂ f′ refl)   = origin h₁ h₂ (r⇒⊗ ∘ f′) refl
  ...
\end{spec}
However, there are many cases---97 in total. The reason for this is
that the possible derivation steps depend on the main connective;
therefore we first have to explore every possible main connective, and
then every possible rule which would produce that main connective.
Because of this, the definition of |find′| is very long and tedious,
and it has mostly been omitted.

From the more general |Origin′| and |find′| we can very easily recover
our original definitions |Origin| and |find| by setting the context
to be empty. In the case of the cut formula |B ⊗ C|, we set the
context to |(_ ⊢> [])| to ensure that the formula ends up at the top
level in the succedent:
\begin{spec}
  Origin  : (f : LG A ⊢ B ⊗ C) → Set
  Origin  f = Origin′  (_ ⊢> []) f

  find    : (f : LG A ⊢ B ⊗ C) → Origin f
  find    f = find′    (_ ⊢> []) f
\end{spec}
And with that, we can finally put the rewrite rules from
\citet{moortgat1999} to use. We can define |trans′| by pattern
matching on the cut formula |B|; applying the appropriate |find|
function to find the monotonicity rule introducing the formula; and
apply the appropriate rewrite rule to create a derivation containing
two cuts on structurally smaller formulas:
\begin{spec}
trans′ : (f : LG A ⊢ B) (g : LG B ⊢ C) → LG A ⊢ C
trans′ {B = el   _}  f g with el.find g
...  | (el.origin       g′  pr) = g′ f
trans′ {B = _ ⊗  _}  f g with ⊗.find f
...  | (⊗.origin h₁ h₂  f′  pr)  = f′ (r⇐⊗ (trans′ h₁ (r⊗⇐ (r⇒⊗ (trans′ h₂ (r⊗⇒ g))))))
trans′ {B = _ ⇐  _}  f g with ⇐.find g
...  | (⇐.origin h₁ h₂  g′  pr)  = g′ (r⊗⇐ (r⇒⊗ (trans′ h₂ (r⊗⇒ (trans′ (r⇐⊗ f) h₁)))))
trans′ {B = _ ⇒  _}  f g with ⇒.find g
...  | (⇒.origin h₁ h₂  g′  pr)  = g′ (r⊗⇒ (r⇐⊗ (trans′ h₁ (r⊗⇐ (trans′ (r⇒⊗ f) h₂)))))
trans′ {B = _ ⊕  _}  f g with ⊕.find g
...  | (⊕.origin h₁ h₂  g′  pr)  = g′ (r⇚⊕ (trans′ (r⊕⇚ (r⇛⊕ (trans′ (r⊕⇛ f) h₂))) h₁))
trans′ {B = _ ⇚  _}  f g with ⇚.find f
...  | (⇚.origin h₁ h₂  f′  pr)  = f′ (r⊕⇚ (r⇛⊕ (trans′ (r⊕⇛ (trans′ h₁ (r⇚⊕ g))) h₂)))
trans′ {B = _ ⇛  _}  f g with ⇛.find f
...  | (⇛.origin h₁ h₂  f′  pr)  = f′ (r⊕⇛ (r⇚⊕ (trans′ (r⊕⇚ (trans′ h₂ (r⇛⊕ g))) h₁)))
\end{spec}


\section{Conclusion}

We have presented the reader with a simple formalisation of the Lambek
Grishin calculus, using the proof assistant Agda. We shown how to formalise
the proof of the admissibility of cut from \citet{moortgat1999} in
Agda, and have extended this proof to cover all of LG.

While we have not covered any of the usual unary operators, the
formalism presented here generalises straightforwardly to accommodate
connectives of any arity---and this extension, together with many
other extensions, are indeed implemented in the full version of our
code.

Most importantly, we hope we presented the reader with a clean and
readable formalisation of the Lambek-Grishin calculus.

\nocite{*}
\bibliographystyle{apalike}
\bibliography{main}

\end{document}
