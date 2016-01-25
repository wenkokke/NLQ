\documentclass{article}
\usepackage{stmaryrd}
\usepackage{comment}
\usepackage{etoolbox}
\usepackage{multicol}
\usepackage{catchfilebetweentags}
\usepackage{appendix}
\usepackage{hyperref}
\usepackage[links]{agda}
\setlength{\mathindent}{0cm}

%%% TODO UPDATE NUMBER MANUALLY -- SIGH
\setcounter{page}{50}

\def\lamET{\lambda^{\rightarrow}_{\{\mathbf{e},\mathbf{t}\}}}%
\DeclareUnicodeCharacter{8852}{$\sqcup$}
\DeclareUnicodeCharacter{8704}{$\forall$}
\DeclareUnicodeCharacter{8866}{$\vdash$}
\DeclareUnicodeCharacter{8656}{$\mathbin{\slash}$}
\DeclareUnicodeCharacter{8658}{$\mathbin{\backslash}$}
\DeclareUnicodeCharacter{8729}{$\bullet$}
\DeclareUnicodeCharacter{8728}{$\circ$}
\DeclareUnicodeCharacter{8678}{$\!\fatslash$}
\DeclareUnicodeCharacter{8680}{$\fatbslash$}
\DeclareUnicodeCharacter{9671}{$\lozenge$}
\DeclareUnicodeCharacter{9633}{$\square$}
\DeclareUnicodeCharacter{9670}{$\blacklozenge$}
\DeclareUnicodeCharacter{9632}{$\blacksquare$}
\DeclareUnicodeCharacter{8639}{$\upharpoonleft$}
\DeclareUnicodeCharacter{8638}{$\upharpoonright$}
\DeclareUnicodeCharacter{8643}{$\downharpoonleft$}
\DeclareUnicodeCharacter{8642}{$\downharpoonright$}
\DeclareUnicodeCharacter{8242}{$'$}
\DeclareUnicodeCharacter{8801}{$\equiv$}
\DeclareUnicodeCharacter{8594}{$\rightarrow$}

\begin{document}
\begin{appendices}

\appendix
\renewcommand{\thesection}{A}
\section{Formalisation of NLQ in Agda}
In this appendix, we will discuss the Agda formalisation of
\emph{focused} NLQ. This section is written in literate Agda, and
includes \emph{all} of the code.
\begin{comment}
\begin{code}
module NLQ_Agda where
\end{code}
\end{comment}
\begin{comment}
\begin{code}
open import Level using (_⊔_)
\end{code}
\end{comment}
The order of presentation is different from the order used in the
thesis, due to constraints on the Agda language.

In the first part of this appendix, we will formalise the syntactic
calculus, NLQ. Then, in the second part, we will implement a
translation from proofs in NLQ to terms in Agda, giving us some form
of semantics.


\subsection{NLQ, Syntactic Calculus}
For our formalisation of NLQ, we are going to abstract over the atomic
types---a luxury offered by the Agda module system. The reason for
this is that the set of atomic types is more-or-less open---sometimes
we find out that we have to add a new one---and can be treated in a
uniform manner. Because atomic types must be assigned a polarity, we
will start out by defining a notion of polarity and polarised values:
\\[1\baselineskip]
\begin{code}
data Polarity : Set where
  + : Polarity
  - : Polarity

record Polarised (A : Set) : Set where
  field
    Pol : A → Polarity
open Polarised {{...}}
\end{code}
\\
We can now open our \AgdaModule{Syntax} module, abstracting over the
type of atomic types and a notion of polarisation for this type:
\\[1\baselineskip]
\begin{code}
module Syntax (Atom : Set) (PolarisedAtom : Polarised Atom) where
\end{code}
\begin{comment}
\begin{code}
  open import Data.Product using (∃; _,_)
  open import Function using (flip; const)
  open import Function.Equality using (_⟨$⟩_)
  open import Function.Equivalence as I using (_⇔_) renaming (equivalence to mkISO)
  open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; inspect)
  open I.Equivalence using (from; to)
\end{code}
\end{comment}



\subsubsection{Types, Structures and Sequents}
First thing to do is to define our types. We abstract a little here:
instead of defining several copies of our rules for $\{\backslash,
\bullet, \slash\}$ and $\{\Diamond,\Box\}$ for new connectives, as we
did in the thesis, we define a datatype to represent the different
kinds of connectives we will be using, and parameterise our
connectives with a kind. We then recover the pretty versions of our
connectives using pattern synonyms. The advantage of this approach is
that we can later-on use e.g.\ the abstract right implication
\AgdaInductiveConstructor{ImpR} in the definitions of the inference
rules, defining all the copies at the same time.
\\[1\baselineskip]
\begin{code}
  data Kind : Set where
    Sol  : Kind -- solid       {⇒, ∙, ⇐}
    Hol  : Kind -- hollow      {⇨, ∘, ⇦}
    Res  : Kind -- reset       {◇, □}
    Ext  : Kind -- extraction  {↿, ↾, ◇↑, □↑}
    Ifx  : Kind -- infixation  {⇃, ⇂, ◇↓, □↓}

  data Type : Set where
    El     : Atom  → Type
    Dia    : Kind  → Type  → Type
    Box    : Kind  → Type  → Type
    _&_     : Type → Type → Type
    UnitR  : Kind  → Type  → Type
    ImpR   : Kind  → Type  → Type  → Type
    ImpL   : Kind  → Type  → Type  → Type
\end{code}
\begin{comment}
\begin{code}
  infix  6 _&_
  infixl 7 _⇐_ _⇦_
  infixr 7 _⇒_ _⇨_
  infix  7 _⇃_ _⇂_
  infix  7 _↿_ _↾_
  infixr 9 ◇_  □_ ◇↓_ □↓_ ◇↑_ □↑_
\end{code}
\end{comment}
\begin{multicols}{2}
\begin{code}
  pattern _⇐_  b a  = ImpL   Sol  b a
  pattern _⇒_  a b  = ImpR   Sol  a b

  pattern _⇨_  a b  = ImpR   Hol  a b
  pattern _⇦_  b a  = ImpL   Hol  b a
  pattern Q    a    = UnitR  Hol  a
  pattern ◇_   a    = Dia    Res  a
  pattern ◇↑_  a    = Dia    Ext  a
  pattern ◇↓_  a    = Dia    Ifx  a
  pattern □_   a    = Box    Res  a
  pattern □↑_  a    = Box    Ext  a
  pattern □↓_  a    = Box    Ifx  a
\end{code}
\end{multicols}
\begin{multicols}{2}
\begin{code}
  pattern _↿_  a b  = ◇↑ □↑ (a ⇒ b)
  pattern _↾_  b a  = ◇↑ □↑ (b ⇐ a)
  pattern _⇃_  a b  = (◇↓ □↓ a) ⇒ b
  pattern _⇂_  b a  = b ⇐ (◇↓ □↓ a)
\end{code}
\end{multicols}
\noindent
We use the same trick in defining structures, and merge Struct$^{+}$
and Struct$^{-}$ together into a single datatype indexed by a
polarity:
\\[1\baselineskip]
\begin{code}
  data Struct : Polarity → Set where
    ·_·   : ∀ {p} → Type → Struct p
    B     : Struct +
    C     : Struct +
    DIA   : Kind → Struct +  → Struct +
    UNIT  : Kind → Struct +
    PROD  : Kind → Struct +  → Struct +  → Struct +
    BOX   : Kind → Struct -  → Struct -
    IMPR  : Kind → Struct +  → Struct -  → Struct -
    IMPL  : Kind → Struct -  → Struct +  → Struct -
\end{code}
\begin{comment}
\begin{code}
  infixr 3 _∙_ _∘_
  infixr 9 ◆_  ■_ ◆↓_ ■↓_ ◆↑_ ■↑_
\end{code}
\end{comment}
\begin{multicols}{2}
\begin{code}
  pattern _∙_  x y  = PROD   Sol  x y
  pattern _∘_  x y  = PROD   Hol  x y
  pattern ◆_   x    = DIA    Res  x
  pattern ◆↑_  x    = DIA    Ext  x
  pattern ◆↓_  x    = DIA    Ifx  x

  pattern I         = UNIT   Hol
  pattern ■_   x    = BOX    Res  x
  pattern ■↑_  x    = BOX    Ext  x
  pattern ■↓_  x    = BOX    Ifx  x
\end{code}
\end{multicols}
\noindent
Since there is no pretty way to write the box we used for focusing in
Unicode, we will have to go with an ugly way:
\\[1\baselineskip]
\begin{comment}
\begin{code}
  infix 2 _⊢_ _⊢[_] [_]⊢_
\end{code}
\end{comment}
\begin{code}
  data Sequent : Set where
    _⊢_    : Struct +  → Struct -  → Sequent
    [_]⊢_  : Type      → Struct -  → Sequent
    _⊢[_]  : Struct +  → Type      → Sequent
\end{code}
\\
And finally, we need to extend our concept of polarity to
\emph{types}:
\\[1\baselineskip]
\begin{code}
  instance
    PolarisedType : Polarised Type
    PolarisedType = record { Pol = Pol′ }
      where
        Pol′ : Type → Polarity
        Pol′ (El    a)      = Pol(a)
        Pol′ (Dia   _ _)    = +
        Pol′ (Box   _ _)    = -
        Pol′ (_ & _)        = +
        Pol′ (UnitR _ _)    = +
        Pol′ (ImpR  _ _ _)  = -
        Pol′ (ImpL  _ _ _)  = -
\end{code}



\subsubsection{Inference Rules}
Below we define the logic of NLQ as a single datatype, indexed by a
sequent. As described in the section on focusing, the axioms and
focusing/unfocusing rules take an extra argument---a piece of evidence
for the polarity of the type \AgdaBound{a}/\AgdaBound{b}:
\\[1\baselineskip]
\begin{comment}
\begin{code}
  infix 1 NLQ_
\end{code}
\end{comment}
\begin{code}
  data NLQ_ : Sequent → Set where
    axElR   : ∀ {b}         → Pol(b) ≡ +  → NLQ · El b · ⊢[ El b ]
    axElL   : ∀ {a}         → Pol(a) ≡ -  → NLQ [ El a ]⊢ · El a ·
    unfR    : ∀ {x b}       → Pol(b) ≡ -  → NLQ x ⊢ · b ·  → NLQ x ⊢[ b ]
    unfL    : ∀ {a y}       → Pol(a) ≡ +  → NLQ · a · ⊢ y  → NLQ [ a ]⊢ y
    focR    : ∀ {x b}       → Pol(b) ≡ +  → NLQ x ⊢[ b ]   → NLQ x ⊢ · b ·
    focL    : ∀ {a y}       → Pol(a) ≡ -  → NLQ [ a ]⊢ y   → NLQ · a · ⊢ y

    impRL   : ∀ {k x y a b} → NLQ x ⊢[ a ]  → NLQ [ b ]⊢ y  → NLQ [ ImpR k a b ]⊢ IMPR k x y
    impRR   : ∀ {k x a b}   → NLQ x ⊢ IMPR k · a · · b ·   → NLQ x ⊢ · ImpR k a b ·
    impLL   : ∀ {k x y a b} → NLQ x ⊢[ a ]  → NLQ [ b ]⊢ y  → NLQ [ ImpL k b a ]⊢ IMPL k y x
    impLR   : ∀ {k x a b}   → NLQ x ⊢ IMPL k · b · · a ·   → NLQ x ⊢ · ImpL k b a ·
    resRP   : ∀ {k x y z}   → NLQ y ⊢ IMPR k x z  → NLQ PROD k x y ⊢ z
    resPR   : ∀ {k x y z}   → NLQ PROD k x y ⊢ z  → NLQ y ⊢ IMPR k x z
    resLP   : ∀ {k x y z}   → NLQ x ⊢ IMPL k z y  → NLQ PROD k x y ⊢ z
    resPL   : ∀ {k x y z}   → NLQ PROD k x y ⊢ z  → NLQ x ⊢ IMPL k z y

    withL1 : ∀ {a1 a2 y}   → NLQ [ a1 ]⊢ y  → NLQ · a1 & a2 · ⊢ y
    withL2 : ∀ {a1 a2 y}   → NLQ [ a2 ]⊢ y  → NLQ · a1 & a2 · ⊢ y
    withR  : ∀ {b1 b2 x}   → NLQ x ⊢ · b1 · → NLQ x ⊢ · b2 · → NLQ x ⊢[ b1 & b2 ]

    diaL    : ∀ {k a y}     → NLQ DIA k · a · ⊢ y  → NLQ · Dia k a · ⊢ y
    diaR    : ∀ {k x b}     → NLQ x ⊢[ b ]         → NLQ DIA k x ⊢[ Dia k b ]
    boxL    : ∀ {k a y}     → NLQ [ a ]⊢ y         → NLQ [ Box k a ]⊢ BOX k y
    boxR    : ∀ {k x b}     → NLQ x ⊢ BOX k · b ·  → NLQ x ⊢ · Box k b ·
    resBD   : ∀ {k x y}     → NLQ x ⊢ BOX k y      → NLQ DIA k x ⊢ y
    resDB   : ∀ {k x y}     → NLQ DIA k x ⊢ y      → NLQ x ⊢ BOX k y

    unitRL  : ∀ {k y a}     → NLQ PROD k · a · (UNIT k) ⊢ y → NLQ · UnitR k a · ⊢ y
    unitRR  : ∀ {k x b}     → NLQ x ⊢[  b ]  → NLQ PROD k x (UNIT k) ⊢[ UnitR k b ]
    unitRI  : ∀ {k x y}     → NLQ x ⊢   y    → NLQ PROD k x (UNIT k) ⊢ y

    dnB     : ∀ {x y z w}   → NLQ x ∙ (y ∘ z) ⊢ w        → NLQ y ∘ ((B ∙ x) ∙ z) ⊢ w
    dnC     : ∀ {x y z w}   → NLQ (x ∘ y) ∙ z ⊢ w        → NLQ x ∘ ((C ∙ y) ∙ z) ⊢ w
    upB     : ∀ {x y z w}   → NLQ y ∘ ((B ∙ x) ∙ z) ⊢ w  → NLQ x ∙ (y ∘ z) ⊢ w
    upC     : ∀ {x y z w}   → NLQ x ∘ ((C ∙ y) ∙ z) ⊢ w  → NLQ (x ∘ y) ∙ z ⊢ w

    extRR   : ∀ {x y z w}   → NLQ ((x ∙ y) ∙ ◆↑ z ⊢ w)  → NLQ (x ∙ (y ∙ ◆↑ z) ⊢ w)
    extLR   : ∀ {x y z w}   → NLQ ((x ∙ y) ∙ ◆↑ z ⊢ w)  → NLQ ((x ∙ ◆↑ z) ∙ y ⊢ w)
    extLL   : ∀ {x y z w}   → NLQ (◆↑ z ∙ (y ∙ x) ⊢ w)  → NLQ ((◆↑ z ∙ y) ∙ x ⊢ w)
    extRL   : ∀ {x y z w}   → NLQ (◆↑ z ∙ (y ∙ x) ⊢ w)  → NLQ (y ∙ (◆↑ z ∙ x) ⊢ w)

    ifxRR   : ∀ {x y z w}   → NLQ (x ∙ (y ∙ ◆↓ z) ⊢ w)  → NLQ ((x ∙ y) ∙ ◆↓ z ⊢ w)
    ifxLR   : ∀ {x y z w}   → NLQ ((x ∙ ◆↓ z) ∙ y ⊢ w)  → NLQ ((x ∙ y) ∙ ◆↓ z ⊢ w)
    ifxLL   : ∀ {x y z w}   → NLQ ((◆↓ z ∙ y) ∙ x ⊢ w)  → NLQ (◆↓ z ∙ (y ∙ x) ⊢ w)
    ifxRL   : ∀ {x y z w}   → NLQ (y ∙ (◆↓ z ∙ x) ⊢ w)  → NLQ (◆↓ z ∙ (y ∙ x) ⊢ w)
\end{code}
\\
Using these axiomatic rules, we can define derived rules. For
instance, we can define the following ``residuation'' rules, which
convert left implication to right implication, and vice versa:
\\[1\baselineskip]
\begin{code}
  resRL : ∀ {k x y z} → NLQ y ⊢ IMPR k x z → NLQ x ⊢ IMPL k z y
  resRL f = resPL (resRP f)

  resLR : ∀ {k x y z} → NLQ x ⊢ IMPL k z y → NLQ y ⊢ IMPR k x z
  resLR f = resPR (resLP f)
\end{code}


\subsubsection{Contexts and Plugging functions}
NLQ might not need contexts and plugging functions for its
specification, but many meta-logical proofs nonetheless require this
vocabulary.
In preparation for the proof in the following section, We will
therefore define a notion of contexts for NLQ.
We start by defining contexts an class of ``pluggable''' things:
\\[1\baselineskip]
\begin{code}
  record Pluggable (C I O : Set) : Set where
    field
      _[_] : C → I → O
  open Pluggable {{...}}
\end{code}
\\
Next, we define the first type of context: full structural
contexts, i.e.\ structures with a single hole. For this, we simply
replicate the structure of contexts, and add the
\AgdaInductiveConstructor{HOLE}-constructor. Note that we replicate
binary constructors twice---once with the hole to the left, and once
with the hole to the right:
\\[1\baselineskip]
\begin{code}
  data StructCtxt (p : Polarity) : Polarity → Set where
    HOLE   : StructCtxt p p
    DIA1   : Kind → StructCtxt p  +  → StructCtxt p  +
    PROD1  : Kind → StructCtxt p  +  → Struct        +  → StructCtxt p  +
    PROD2  : Kind → Struct        +  → StructCtxt p  +  → StructCtxt p  +
    BOX1   : Kind → StructCtxt p  -  → StructCtxt p  -
    IMPR1  : Kind → StructCtxt p  +  → Struct        -  → StructCtxt p  -
    IMPR2  : Kind → Struct        +  → StructCtxt p  -  → StructCtxt p  -
    IMPL1  : Kind → StructCtxt p  -  → Struct        +  → StructCtxt p  -
    IMPL2  : Kind → Struct        -  → StructCtxt p  +  → StructCtxt p  -
\end{code}
\\
Plugging is simply the process of taking a given structure, and
inserting this in place of the hole:
\\[1\baselineskip]
\begin{code}
  instance
    Pluggable-Struct : ∀ {p1 p2} → Pluggable (StructCtxt p1 p2) (Struct p1) (Struct p2)
    Pluggable-Struct = record { _[_] = _[_]′ }
      where
        _[_]′ : ∀ {p1 p2} → StructCtxt p1 p2 → Struct p1 → Struct p2
        ( HOLE          ) [ z ]′ = z
        ( DIA1   k x    ) [ z ]′ = DIA   k    (x [ z ]′)
        ( PROD1  k x y  ) [ z ]′ = PROD  k    (x [ z ]′) y
        ( PROD2  k x y  ) [ z ]′ = PROD  k x  (y [ z ]′)
        ( BOX1   k x    ) [ z ]′ = BOX   k    (x [ z ]′)
        ( IMPR1  k x y  ) [ z ]′ = IMPR  k    (x [ z ]′) y
        ( IMPR2  k x y  ) [ z ]′ = IMPR  k x  (y [ z ]′)
        ( IMPL1  k x y  ) [ z ]′ = IMPL  k    (x [ z ]′) y
        ( IMPL2  k x y  ) [ z ]′ = IMPL  k x  (y [ z ]′)
\end{code}
\\
In accordance with our approach in the previous sections, we recover
more specific (and prettier) context-constructors using pattern
synonyms:
\begin{multicols}{2}
\begin{code}
  pattern _<∙_  x y  = PROD1  Sol  x y
  pattern _<⇒_  x y  = IMPR2  Sol  x y
  pattern _<⇐_  y x  = IMPL1  Sol  y x
  pattern _<∘_  x y  = PROD1  Hol  x y
  pattern _<⇨_  x y  = IMPR1  Hol  x y
  pattern _<⇦_  y x  = IMPL1  Hol  y x
  pattern _∙>_  x y  = PROD2  Sol  x y
  pattern _⇒>_  x y  = IMPR2  Sol  x y
  pattern _⇐>_  y x  = IMPL1  Sol  y x
  pattern _∘>_  x y  = PROD2  Hol  x y
  pattern _⇨>_  x y  = IMPR2  Hol  x y
  pattern _⇦>_  y x  = IMPL2  Hol  y x
\end{code}
\end{multicols}
\begin{multicols}{2}
\begin{code}
  pattern ◆>_   x    = DIA1   Res  x
  pattern ◆↓>_  x    = DIA1   Ext  x
  pattern ◆↑>_  x    = DIA1   Ifx  x
  pattern ■>_   x    = BOX1   Res  x
  pattern ■↓>_  x    = BOX1   Ext  x
  pattern ■↑>_  x    = BOX1   Ifx  x
\end{code}
\end{multicols}
\noindent
And we do the same for sequents:
\\[1\baselineskip]
\begin{code}
  data SequentCtxt (p : Polarity) : Set where
    _<⊢_  : StructCtxt p  + → Struct        - → SequentCtxt p
    _⊢>_  : Struct        + → StructCtxt p  - → SequentCtxt p

  instance
    Pluggable-Sequent : ∀ {p} → Pluggable (SequentCtxt p) (Struct p) Sequent
    Pluggable-Sequent = record { _[_] = _[_]′ }
      where
        _[_]′ : ∀ {p} → SequentCtxt p → Struct p → Sequent
        (x <⊢ y)  [ z ]′ = x [ z ] ⊢ y
        (x ⊢> y)  [ z ]′ = x ⊢ y [ z ]
\end{code}



\subsubsection{Display Property}
In this section, we will prove that NLQ has the display
property. Before we can do this, we will define one more type of
context: a display context. This is a context where the inserted
structure is always guaranteed to end up at the top-level:
\\[1\baselineskip]
\begin{code}
  data DisplayCtxt : Polarity → Set where
    <⊢_  : Struct -  → DisplayCtxt +
    _⊢>  : Struct +  → DisplayCtxt -

  instance
    Pluggable-Display : ∀ {p} → Pluggable (DisplayCtxt p) (Struct p) Sequent
    Pluggable-Display = record { _[_] = _[_]′ }
      where
        _[_]′ : ∀ {p} → DisplayCtxt p → Struct p → Sequent
        (<⊢ y)  [ x ]′  = x ⊢ y
        (x ⊢>)  [ y ]′  = x ⊢ y
\end{code}
\\
Now we can defined \AgdaFunction{DP}: a type-level function, which
takes a sequent context and computes a display context in which the
structure that would be in the hole of the sequent context is
displayed (i.e. brought to the top-level).

This is implemented with two functions, \AgdaFunction{DPL} and
\AgdaFunction{DPR}, which manipulate the antecedent and succedent. By
splitting up the sequent in two arguments---the antecedent and the
succedent---these functions become structurally recursive. Note that
what these functions encode is basically the relations established by
residuation:
\\[1\baselineskip]
\begin{code}
  mutual
    DP : ∀ {p} (s : SequentCtxt p) → DisplayCtxt p
    DP (x <⊢ y) = DPL x y
    DP (x ⊢> y) = DPR x y

    DPL : ∀ {p} (x : StructCtxt p +) (y : Struct -) → DisplayCtxt p
    DPL ( HOLE          ) z = <⊢ z
    DPL ( DIA1   k x    ) z = DPL x  ( BOX   k z    )
    DPL ( PROD1  k x y  ) z = DPL x  ( IMPL  k z y  )
    DPL ( PROD2  k x y  ) z = DPL y  ( IMPR  k x z  )

    DPR : ∀ {p} (x : Struct +) (y : StructCtxt p -) → DisplayCtxt p
    DPR x  ( HOLE          ) = x ⊢>
    DPR x  ( BOX1   k y    ) = DPR    ( DIA   k x    ) y
    DPR x  ( IMPR1  k y z  ) = DPL y  ( IMPL  k z x  )
    DPR x  ( IMPR2  k y z  ) = DPR    ( PROD  k y x  ) z
    DPR x  ( IMPL1  k z y  ) = DPR    ( PROD  k x y  ) z
    DPR x  ( IMPL2  k z y  ) = DPL y  ( IMPR  k x z  )
\end{code}
\\
The actual displaying is done by the term-level function
\AgdaFunction{dp}. This function takes a sequent context $s$ (as
above), a structure $w$, and a proof for the sequent $s [ w ]$. It
then computes an isomorphism between proofs of $s [ w ]$ and proofs of
$\AgdaFunction{DP}(s)[ w ]$ where, in the second proof, the structure
$w$ is guaranteed  to be displayed:\footnote{%
  In the definition of \AgdaFunction{dp} we use some definitions from
  the Agda standard library, related to isomorphisms, found under
  \AgdaFunction{Function.Equivalence}. An isomorphism is written
  \AgdaFunction{⇔}, and created with \AgdaFunction{mkISO}---which was
  renamed from \AgdaFunction{equivalence}. Identity and composition
  are written as usual, with the module prefix \AgdaFunction{I}.
  Application is written with a combination of
  \AgdaField{from}/\AgdaField{to} and \AgdaFunction{⟨\$⟩}.
}
\\[1\baselineskip]
\begin{code}
  mutual
    dp : ∀ {p} (s : SequentCtxt p) (w : Struct p) → (NLQ s [ w ]) ⇔ (NLQ DP(s)[ w ])
    dp (x <⊢ y) w = dpL x y w
    dp (x ⊢> y) w = dpR x y w

    dpL  : ∀ {p} (x : StructCtxt p +) (y : Struct -) (w : Struct p)
         → (NLQ x [ w ] ⊢ y) ⇔ (NLQ DPL x y [ w ])
    dpL ( HOLE          )  z w = I.id
    dpL ( DIA1   k x    )  z w = dpL x  ( BOX   k z    )  w I.∘ mkISO resDB resBD
    dpL ( PROD1  k x y  )  z w = dpL x  ( IMPL  k z y  )  w I.∘ mkISO resPL resLP
    dpL ( PROD2  k x y  )  z w = dpL y  ( IMPR  k x z  )  w I.∘ mkISO resPR resRP

    dpR  : ∀ {p} (x : Struct +) (y : StructCtxt p -) (w : Struct p)
         → (NLQ x ⊢ y [ w ]) ⇔ (NLQ DPR x y [ w ])
    dpR x ( HOLE          ) w = I.id
    dpR x ( BOX1   k y    ) w = dpR    ( DIA   k x    ) y  w I.∘ mkISO resBD resDB
    dpR x ( IMPR1  k y z  ) w = dpL y  ( IMPL  k z x  )    w I.∘ mkISO resRL resLR
    dpR x ( IMPR2  k y z  ) w = dpR    ( PROD  k y x  ) z  w I.∘ mkISO resRP resPR
    dpR x ( IMPL1  k z y  ) w = dpR    ( PROD  k x y  ) z  w I.∘ mkISO resLP resPL
    dpR x ( IMPL2  k z y  ) w = dpL y  ( IMPR  k x z  )    w I.∘ mkISO resLR resRL
\end{code}
\\
Note that while they are defined under a \AgdaKeyword{mutual}-keyword,
these functions are not mutually recursive---however, if the logic NLQ
contained e.g.\ subtractive types as found in LG, they would be.

Below we define \AgdaFunction{dp1} and \AgdaFunction{dp2}, which are
helper functions. These functions allow you to access the two sides of
the isomorphism more easily:
\\[1\baselineskip]
\begin{code}
  dp1 : ∀ {p} (s : SequentCtxt p) (w : Struct p) → NLQ s [ w ] → NLQ DP(s)[ w ]
  dp1 s w f = to (dp s w) ⟨$⟩ f

  dp2 : ∀ {p} (s : SequentCtxt p) (w : Struct p) → NLQ DP(s)[ w ] → NLQ s [ w ]
  dp2 s w f = from (dp s w) ⟨$⟩ f
\end{code}



\subsubsection{Structuralising Types}
Because each logical connective has a structural equivalent, it is
possible---to a certain ifxend---structuralise logical connectives
en masse. The function \AgdaFunction{St} takes a type, and computes
the maximally structuralised version of that type, given a target
polarity $p$:
\\[1\baselineskip]
\begin{code}
  St : ∀ {p} → Type → Struct p
  St { p = + } ( Dia    k  a   )  = DIA   k (St a)
  St { p = - } ( Box    k  a   )  = BOX   k (St a)
  St { p = + } ( UnitR  k  a   )  = PROD  k (St a) (UNIT k)
  St { p = - } ( ImpR   k  a b )  = IMPR  k (St a) (St b)
  St { p = - } ( ImpL   k  b a )  = IMPL  k (St b) (St a)
  St { p = _ } a                  = · a ·
\end{code}
\\
We know that if we try to structuralise a positive type as a negative
structure, or vice versa, it results in the primitive structure. The
lemmas \AgdaFunction{lem-Neg-St} and \AgdaFunction{lem-Pos-St} encode
this knowledge:
\\[1\baselineskip]
\begin{code}
  lem-Neg-St : ∀ a → Pol(a) ≡ - → St { + } a ≡ · a ·
  lem-Neg-St ( El        a    ) n = refl
  lem-Neg-St ( Dia    k  a    ) ()
  lem-Neg-St ( Box    k  a    ) n = refl
  lem-Neg-St ( a & b          ) ()
  lem-Neg-St ( UnitR  k  a    ) ()
  lem-Neg-St ( ImpR   k  a b  ) n = refl
  lem-Neg-St ( ImpL   k  b a  ) n = refl

  lem-Pos-St : ∀ a → Pol(a) ≡ + → St { - } a ≡ · a ·
  lem-Pos-St ( El        a    ) p = refl
  lem-Pos-St ( Dia    k  a    ) p = refl
  lem-Pos-St ( Box    k  a    ) ()
  lem-Pos-St ( a & b          ) p = refl
  lem-Pos-St ( UnitR  k  a    ) p = refl
  lem-Pos-St ( ImpR   k  a b  ) ()
  lem-Pos-St ( ImpL   k  b a  ) ()
\end{code}
\\
The functions \AgdaFunction{st}, \AgdaFunction{stL} and
\AgdaFunction{stR} actually perform the structuralisation described by
\AgdaFunction{St}. Given a proof for a sequent $s$, they will
structuralise either the antecedent, the succedent, or both:
\\[1\baselineskip]
\begin{code}
  mutual
    st : ∀ {a b} → NLQ St a ⊢ St b → NLQ · a · ⊢ · b ·
    st f = stL (stR f)

    stL : ∀ {a y} → NLQ St a ⊢ y → NLQ · a · ⊢ y
    stL { a = El        a    } f = f
    stL { a = Dia    k  a    } f = diaL (resBD (stL (resDB f)))
    stL { a = Box    k  a    } f = f
    stL { a = a & b          } f = f
    stL { a = UnitR  k  a    } f = unitRL (resLP (stL (resPL f)))
    stL { a = ImpR   k  a b  } f = f
    stL { a = ImpL   k  b a  } f = f

    stR : ∀ {x b} → NLQ x ⊢ St b → NLQ x ⊢ · b ·
    stR { b = El        a    } f = f
    stR { b = Dia    k  a    } f = f
    stR { b = Box    k  a    } f = boxR (resDB (stR (resBD f)))
    stR { b = a & b          } f = f
    stR { b = UnitR  k  a    } f = f
    stR { b = ImpR   k  a b  } f = impRR (resPR (stR (resLP (stL (resPL (resRP f))))))
    stR { b = ImpL   k  b a  } f = impLR (resPL (stR (resRP (stL (resPR (resLP f))))))
\end{code}




\subsubsection{Identity Expansion}
Another important proof is `identity expansion'---the proof
that tells us that although we have restricted the axioms to atomic
types, we can still derive the full identity rule.
The inclusion of focusing makes this proof slightly more complex, as
between the introduction of the connectives, we have to structuralise
and occasionally switch focus.

In the below proof, \AgdaFunction{axR} and \AgdaFunction{axL}
recursively apply the rules for symmetric introduction---through
\AgdaFunction{axR′} and \AgdaFunction{axL′}---until there is
a clash in polarity---which is defined as applying \AgdaFunction{axR}
to a negative type or vice versa---at which point they switch focus,
structuralise, and continue:\footnote{%
  In the definition of \AgdaFunction{ax}, \AgdaFunction{axR} and
  \AgdaFunction{axL} we use \AgdaFunction{inspect}, which allows you
  to apply a function \AgdaBound{f} to an argument \AgdaBound{x} to
  obtain \AgdaBound{y}, and obtain an explicit proof that
  \AgdaBound{f} \AgdaBound{x} \AgdaFunction{≡} \AgdaBound{y}.
  The function \AgdaFunction{inspect} is defined in
  \AgdaFunction{Relation.Binary.PropositionalEquality}.
}
\\[1\baselineskip]
\begin{code}
  mutual
    ax : ∀ {a} → NLQ · a · ⊢ · a ·
    ax {a} with Pol(a) | inspect Pol(a)
    ... | + | P.[ p ]  rewrite lem-Pos-St  a p  = stL (focR p (axR′ p))
    ... | - | P.[ n ]  rewrite lem-Neg-St  a n  = stR (focL n (axL′ n))

    axR : ∀ {b} → NLQ St b ⊢[ b ]
    axR {b} with Pol(b) | inspect Pol(b)
    ... | + | P.[ p ]                           = axR′ p
    ... | - | P.[ n ]  rewrite lem-Neg-St  b n  = unfR n (stR (focL n (axL′ n)))

    axL : ∀ {a} → NLQ [ a ]⊢ St a
    axL {a} with Pol(a) | inspect Pol(a)
    ... | + | P.[ p ]  rewrite lem-Pos-St  a p  = unfL p (stL (focR p (axR′ p)))
    ... | - | P.[ n ]                           = axL′ n

    axR′ : ∀ {b} → Pol(b) ≡ + → NLQ St b ⊢[ b ]
    axR′ { b = El        a    } p = axElR p
    axR′ { b = Dia    k  a    } p = diaR axR
    axR′ { b = Box    k  a    } ()
    axR′ { b = a & b          } p = withR (stR (withL1 axL)) (stR (withL2 axL))
    axR′ { b = UnitR  k  a    } p = unitRR axR
    axR′ { b = ImpR   k  a b  } ()
    axR′ { b = ImpL   k  b a  } ()

    axL′ : ∀ {a} → Pol(a) ≡ - → NLQ [ a ]⊢ St a
    axL′ { a = El        a    } n = axElL n
    axL′ { a = Dia    k  a    } ()
    axL′ { a = Box    k  a    } n = boxL axL
    axL′ { a = a & b          } ()
    axL′ { a = UnitR  k  a    } ()
    axL′ { a = ImpR   k  a b  } n = impRL axR axL
    axL′ { a = ImpL   k  b a  } n = impLL axR axL
\end{code}

\subsubsection{Quanfitier Raising}
In this section, we show that $\mathbf{Q}\uparrow$ and
$\mathbf{Q}\downarrow$ are indeed derivable in the calculus NLQ. For
this, we define yet another type of context: the
\AgdaFunction{∙-Ctxt}, i.e.\ contexts made up solely out of solid
products:
\\[1\baselineskip]
\begin{code}
  data ∙-Ctxt : Set where
    HOLE   : ∙-Ctxt
    PROD1  : ∙-Ctxt    → Struct +  → ∙-Ctxt
    PROD2  : Struct +  → ∙-Ctxt    → ∙-Ctxt

  instance
    Pluggable-∙ : Pluggable ∙-Ctxt (Struct +) (Struct +)
    Pluggable-∙ = record { _[_] = _[_]′ }
      where
        _[_]′ : ∙-Ctxt → Struct + → Struct +
        ( HOLE        ) [ z ]′ = z
        ( PROD1  x y  ) [ z ]′ = PROD Sol    (x [ z ]′) y
        ( PROD2  x y  ) [ z ]′ = PROD Sol x  (y [ z ]′)
\end{code}
\\
For these contexts, we can define the \AgdaFunction{trace} function,
which inserts the correct trace of \textbf{I}'s, \textbf{B}'s and
\textbf{C}'s:
\\[1\baselineskip]
\begin{code}
  trace : ∙-Ctxt → Struct +
  trace ( HOLE        )  = UNIT Hol
  trace ( PROD1  x y  )  = PROD Sol (PROD Sol C (trace x)) y
  trace ( PROD2  x y  )  = PROD Sol (PROD Sol B x) (trace y)
\end{code}
\\
And using the \AgdaFunction{trace} function, we can define upwards and
downwards quantifier movement:
\\[1\baselineskip]
\begin{code}
  q↑ : ∀ {y b c} → ∀ x → NLQ trace(x) ⊢[ b ] → NLQ [ c ]⊢ y → NLQ x [ · Q (c ⇦ b) · ] ⊢ y
  q↑ x f g = ↑ x (resLP (focL refl (impLL f g)))
    where
    ↑ : ∀ {a z} x → NLQ · a · ∘ trace(x) ⊢ z → NLQ x [ · Q a · ] ⊢ z
    ↑ x f = init x (move x f)
      where
      init  : ∀ {a z} (x : ∙-Ctxt) → NLQ x [ · a · ∘ I ] ⊢ z → NLQ x [ · Q a · ] ⊢ z
      init  ( HOLE        ) f = unitRL f
      init  ( PROD1  x y  ) f = resLP (init x (resPL f))
      init  ( PROD2  x y  ) f = resRP (init y (resPR f))
      move  : ∀ {y z} (x : ∙-Ctxt) → NLQ y ∘ trace(x) ⊢ z → NLQ x [ y ∘ I ] ⊢ z
      move  ( HOLE        ) f = f
      move  ( PROD1  x y  ) f = resLP (move x (resPL (upC f)))
      move  ( PROD2  x y  ) f = resRP (move y (resPR (upB f)))

  q↓ : ∀ {a b} → ∀ x → NLQ x [ · a · ] ⊢ · b · → NLQ trace(x) ⊢ · a ⇨ b ·
  q↓ x f = impRR (resPR (↓ x f))
    where
    ↓ : ∀ {y z} x → NLQ x [ y ] ⊢ z → NLQ y ∘ trace(x) ⊢ z
    ↓ ( HOLE        ) f = unitRI f
    ↓ ( PROD1  x y  ) f = dnC (resLP (↓ x (resPL f)))
    ↓ ( PROD2  x y  ) f = dnB (resRP (↓ y (resPR f)))
\end{code}



\subsubsection{Infixation and Reasoning with Gaps}
The final type of movement to discuss is the derived version of the
R$_{rgap}$ rules used by Barker and Shan (2015). First we will
formalise the right infixation, allowing a structure with an
infixation licence to move downwards past solid products:
\\[1\baselineskip]
\begin{code}
  ifxR : ∀ {y z w} (x : ∙-Ctxt) → NLQ x [ y ∙ ◆↓ z ] ⊢ w → NLQ x [ y ] ∙ ◆↓ z ⊢ w
  ifxR ( HOLE        ) f = f
  ifxR ( PROD1  x y  ) f = ifxLR (resLP (ifxR x (resPL f)))
  ifxR ( PROD2  x y  ) f = ifxRR (resRP (ifxR y (resPR f)))
\end{code}
\\
However, here we run into a slight problem. In this formalisation, we
use focusing. However, we do not have a full adaptation of the
normalisation procedure from display NLQ to focused NLQ to NLQ.
In order to fully encode Barker and Shan's rule, we would have to
infixate and then \emph{remove} the license. However, removing the
license \emph{in this context} is only possible in the case where the
type under the licence is positive. So, without problems, we can
define the following version of the rule:
\\[1\baselineskip]
\begin{code}
  r⇂⁺  : ∀ {y b c} (x : ∙-Ctxt) (pr : Pol(b) ≡ +)
       → NLQ x [ y ∙ · b · ] ⊢ · c · →  NLQ x [ y ] ⊢ · c ⇂ b ·
  r⇂⁺ {y} {b} x pr f = impLR (resPL (resRP (diaL (resPR (ifxR x (stop x f))))))
    where
    stop : ∀ {z} (x : ∙-Ctxt) → NLQ x [ y ∙ · b · ] ⊢ z → NLQ x [ y ∙ ◆↓ · □↓ b · ] ⊢ z
    stop ( HOLE        ) f = resRP (resBD (focL refl (boxL (unfL pr (resPR f)))))
    stop ( PROD1  x y  ) f = resLP (stop x (resPL f))
    stop ( PROD2  x y  ) f = resRP (stop y (resPR f))
\end{code}
\\
However, in the case where the type under the licence is negative, we
will have to use the following, more general rule which leaves the
license in place, and then remove it at a later stage in the proof:
\\[1\baselineskip]
\begin{code}
  r⇂ : ∀ {y b c} (x : ∙-Ctxt) → NLQ x [ y ∙ ◆↓ · □↓ b · ] ⊢ · c · →  NLQ x [ y ] ⊢ · c ⇂ b ·
  r⇂ x f = impLR (resPL (resRP (diaL (resPR (ifxR x f)))))
\end{code}
\\
The proofs for left infixation, and extraction can be done in a
similar manner.


\subsection{Semantics in Agda}
Having formalised the syntactic calculus NLQ in the first part, we
will now briefly turn our attention towards a semantics. Instead of
formalising $\lambda^{\rightarrow}_{\{\mathbf{e},\mathbf{t}\}}$, we
will give the semantics for NLQ in Agda---it looks much nicer, and is
much less work, even if $\lambda\Pi$ is a little bit more expressive
than strictly necessary.

We will give our semantics in a separate module, which will---once
again---be abstracting over atomic types and their polarity. In
addition to this, we now have to abstract over a translation from atomic
types to semantic types. For this, we define the following class of
translations:
\\[1\baselineskip]
\begin{code}
record Translate {t1 t2} (T1 : Set t1) (T2 : Set t2) : Set (t1 ⊔ t2) where
  field
    _* : T1 → T2
open Translate {{...}}
\end{code}
\\
And abstract accordingly:
\\[1\baselineskip]
\begin{code}
module Semantics
  (Atom : Set)
  (PolarisedAtom   : Polarised Atom)
  (TranslateAtom   : Translate Atom Set)
  where
\end{code}
\begin{comment}
\begin{code}
  open import Function     using (id; flip; _∘_)
  open import Data.Unit    using (⊤; tt)
  open import Data.Product using (_×_; _,_)
  open module NLQ = Syntax Atom PolarisedAtom hiding (_∘_)
\end{code}
\end{comment}
\\
The translation on types, structures and sequents is rather
simple. Instead of translating sequents to sequents, we will translate
them to function types. Implications too, both logical and structural,
become function types. Otherwise, products become products, units
becomes units, etc.
\\[1\baselineskip]
\begin{code}
  instance
    TranslateType : Translate Type Set
    TranslateType = record { _* = _*′ }
      where
        _*′ : Type → Set
        El        a    *′ = a *
        Dia    _  a    *′ = a *′
        Box    _  a    *′ = a *′
        (a & b)        *′ = a *′ × b *′
        UnitR  _  a    *′ = a *′
        ImpR   _  a b  *′ = a *′ → b *′
        ImpL   _  b a  *′ = a *′ → b *′

    TranslateStruct : ∀ {p} → Translate (Struct p) Set
    TranslateStruct = record { _* = _*′ }
      where
        _*′ : ∀ {p} → Struct p → Set
        · a ·         *′ = a *
        B             *′ = ⊤
        C             *′ = ⊤
        DIA   _  x    *′ = x *′
        UNIT  _       *′ = ⊤
        PROD  _  x y  *′ = x *′ × y *′
        BOX   _  x    *′ = x *′
        IMPR  _  x y  *′ = x *′ → y *′
        IMPL  _  y x  *′ = x *′ → y *′

    TranslateSequent : Translate Sequent Set
    TranslateSequent = record { _* = _*′ }
      where
        _*′ : Sequent → Set
        ( x ⊢ y     )*′ = x * → y *
        ( [ a ]⊢ y  )*′ = a * → y *
        ( x ⊢[ b ]  )*′ = x * → b *
\end{code}
\\
Finally, using our translation on sequents, we can implement the
translation on proofs:
\\[1\baselineskip]
\begin{code}
  instance
    TranslateProof : ∀ {s} → Translate (NLQ s) (s *)
    TranslateProof = record { _* = _*′ }
      where
        _*′ : ∀ {s} → NLQ s → s *
        axElR _      *′ = id
        axElL _      *′ = id
        unfR  _ f    *′ = f *′
        unfL  _ f    *′ = f *′
        focR  _ f    *′ = f *′
        focL  _ f    *′ = f *′
        impRL   f g  *′ = λ h → g *′ ∘ h ∘ f *′
        impRR   f    *′ = f *′
        impLL   f g  *′ = λ h → g *′ ∘ h ∘ f *′
        impLR   f    *′ = f *′
        resRP   f    *′ = λ{ (x , y)  → (f *′)  y   x   }
        resLP   f    *′ = λ{ (x , y)  → (f *′)  x   y   }
        resPR   f    *′ = λ{  y   x   → (f *′) (x , y)  }
        resPL   f    *′ = λ{  x   y   → (f *′) (x , y)  }
        withL1  f    *′ = λ{ (x , y)  → (f *′)  x }
        withL2  f    *′ = λ{ (x , y)  → (f *′)  y }
        withR   f g  *′ = λ x → ((f *′) x , (g *′) x)
        diaL    f    *′ = f *′
        diaR    f    *′ = f *′
        boxL    f    *′ = f *′
        boxR    f    *′ = f *′
        resBD   f    *′ = f *′
        resDB   f    *′ = f *′
        unitRL  f    *′ = λ{  x       → (f *′) (x , _)  }
        unitRR  f    *′ = λ{ (x , _)  → (f *′)  x       }
        unitRI  f    *′ = λ{ (x , _)  → (f *′)  x       }
        dnB     f    *′ = λ{ ( y , (_ , x) , z)  → (f *′) ( x , y  , z) }
        dnC     f    *′ = λ{ ( x , (_ , y) , z)  → (f *′) ((x , y) , z) }
        upB     f    *′ = λ{ ( x , y   , z)  → (f *′) ( y , (_ , x) , z) }
        upC     f    *′ = λ{ ((x , y)  , z)  → (f *′) ( x , (_ , y) , z) }
        extRR   f    *′ = λ{ ( x , y   , z)  → (f *′) ((x , y) , z)  }
        extLR   f    *′ = λ{ ((x , z)  , y)  → (f *′) ((x , y) , z)  }
        extLL   f    *′ = λ{ ((z , y)  , x)  → (f *′) ( z , y  , x)  }
        extRL   f    *′ = λ{ ( y , z   , x)  → (f *′) ( z , y  , x)  }
        ifxRR   f    *′ = λ{ ((x , y)  , z)  → (f *′) ( x , y  , z)  }
        ifxLR   f    *′ = λ{ ((x , y)  , z)  → (f *′) ((x , z) , y)  }
        ifxLL   f    *′ = λ{ ( z , y   , x)  → (f *′) ((z , y) , x)  }
        ifxRL   f    *′ = λ{ ( z , y   , x)  → (f *′) ( y , z  , x)  }
\end{code}


\subsection{Example}
We will end the Agda formalisation with a small example. For this, we
need to instantiate the syntax and semantics modules. We start by
defining atomic types, and a concept of polarisation---everything has
negative polarity:
\\[1\baselineskip]
\begin{comment}
\begin{code}
module Example where
  open import Data.Product using (_,_)
  open import Relation.Binary.PropositionalEquality using (refl) renaming (_≡_ to _↦_)
\end{code}
\end{comment}
\begin{code}
  data Atom : Set where S N NP : Atom

  PolarisedAtom : Polarised Atom
  PolarisedAtom = record { Pol = λ _ → - }
\end{code}
\\
If we want to translate these atomic types to Agda, we will need some
target types. Agda has a built-in type for Booleans, but we are not
really interested in computing anything, so we will simply postulate
everything:
\\[1\baselineskip]
\begin{code}
  postulate
    Bool    : Set
    exists  : {a : Set} → (a → Bool) → Bool
    forAll  : {a : Set} → (a → Bool) → Bool
    _⊃_     : Bool → Bool → Bool
    _∧_     : Bool → Bool → Bool

    Entity  : Set
    mary    : Entity
    see     : Entity → Entity → Bool
    fox     : Entity → Bool
\end{code}
\\
The translation function then follows, and with it we can instantiate
the syntax and semantics modules:
\\[1\baselineskip]
\begin{code}
  TranslateAtom : Translate Atom Set
  TranslateAtom = record { _* = _*′ }
    where
      _*′  : Atom → Set
      S   *′ = Bool
      N   *′ = Entity → Bool
      NP  *′ = Entity

  open Syntax     Atom PolarisedAtom
  open Semantics  Atom PolarisedAtom TranslateAtom
\end{code}
\\
Then we define the syntactic types for our example sentence. There are
much better ways to do this---building a lexicon, computing the
sequent from the given words, etc---and many of these are used in the
Haskell implementation, but since the Agda version lacks proof search,
there is no real reason to invest in all this machinery:
\\[1\baselineskip]
\begin{code}
  MARY SEES FOXES : Struct +
  MARY   = · El NP ·
  SEES   = · (El NP ⇒ El S) ⇐ El NP ·
  FOXES  = · Q(El S ⇦ (El NP ⇨ El S)) ·
\end{code}
\\
A proof for this sentence is easily given:
\\[1\baselineskip]
\begin{code}
  syn0  : NLQ MARY ∙ SEES ∙ FOXES ⊢ · El S ·
  syn0  =  q↑ (PROD2 _ (PROD2 _ HOLE)) (unfR refl
        (  q↓ (PROD2 _ (PROD2 _ HOLE)) (resRP (resLP (focL refl
        (  impLL axR (impRL axR axL))))))) axL
\end{code}
\\
We then give some definitions for our lexical entries. Of course,
\AgdaPostulate{mary} already has a definition. The real work is done
in the definition of \AgdaFunction{foxes}:
\\[1\baselineskip]
\begin{code}
  sees : SEES *
  sees y x = see x y

  foxes : FOXES *
  foxes v = exists {Entity → Bool} (λ f → forAll {Entity} (λ x → f x ⊃ (fox x ∧ v x)))
\end{code}
\\
And finally, we translate our syntactic proof, insert the lexical
entries, and normalise, et voil\`{a}! We have our semantics:
\\[1\baselineskip]
\begin{code}
  sem0 : Bool
  sem0 = (syn0 *) (mary , sees , foxes)

  red0 : sem0 ↦ exists (λ f → forAll (λ x → f x ⊃ (fox x ∧ see mary x)))
  red0 = refl
\end{code}

\end{appendices}
\end{document}
