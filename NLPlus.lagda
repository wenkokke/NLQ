\documentclass{article}
\usepackage{hyperref}
\usepackage[links]{agda}
\let\oldcode\code
\def\code{\vspace{0.5\baselineskip}\oldcode}
\let\oldendcode\endcode
\def\endcode{\oldendcode\vspace{0.5\baselineskip}}
\usepackage{stmaryrd}
\usepackage{comment}
\usepackage{multicol}
\usepackage{catchfilebetweentags}
\usepackage{appendix}
\setlength{\mathindent}{0pt}
\DeclareUnicodeCharacter{8852}{$\sqcup$}
\DeclareUnicodeCharacter{8704}{$\forall$}
\DeclareUnicodeCharacter{8866}{$\vdash$}
\DeclareUnicodeCharacter{8656}{$\mathbin{\slash}$}
\DeclareUnicodeCharacter{8658}{$\mathbin{\backslash}$}
\DeclareUnicodeCharacter{8729}{$\bullet$}
\DeclareUnicodeCharacter{8728}{$\circ$}
\DeclareUnicodeCharacter{8678}{$\!\fatslash$}
\DeclareUnicodeCharacter{8680}{$\fatbslash$}
\DeclareUnicodeCharacter{9671}{$\Diamond$}
\DeclareUnicodeCharacter{9633}{$\Box$}
\DeclareUnicodeCharacter{9670}{$\Diamond$}
\DeclareUnicodeCharacter{9632}{$\Box$}
\DeclareUnicodeCharacter{8639}{$\upharpoonleft$}
\DeclareUnicodeCharacter{8638}{$\upharpoonright$}
\DeclareUnicodeCharacter{8643}{$\downharpoonleft$}
\DeclareUnicodeCharacter{8642}{$\downharpoonright$}
\DeclareUnicodeCharacter{8242}{$'$}
\DeclareUnicodeCharacter{8801}{$\equiv$}
\DeclareUnicodeCharacter{8594}{$\rightarrow$}
\begin{document}
\begin{appendices}

\section{Formalisation of NLPlus in Agda}
\begin{code}
module NLPlus where
\end{code}

\begin{comment}
\begin{code}
open import Level          using (_⊔_)
open import Category.Monad using (module RawMonad; RawMonad)
\end{code}
\end{comment}

\begin{code}
data Polarity : Set where
  + : Polarity
  - : Polarity
\end{code}

\begin{code}
record Polarised (A : Set) : Set where
  field
    Pol : A → Polarity
open Polarised {{...}}
\end{code}

\begin{code}
record Translate {t1 t2} (T1 : Set t1) (T2 : Set t2) : Set (t1 ⊔ t2) where
  field
    _* : T1 → T2
open Translate {{...}}
\end{code}

\subsection{NLPlus, Syntactic Calculus}
\begin{code}
module Syntax (Atom : Set) (PolarisedAtom : Polarised Atom) where
\end{code}

\begin{comment}
\begin{code}
  open import Data.Product                               using (∃; _,_)
  open import Function                                   using (flip; const)
  open import Function.Equality                          using (_⟨$⟩_)
  open import Function.Equivalence                  as I using (_⇔_) renaming (equivalence to mkISO)
  open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; inspect)
  open I.Equivalence using (from; to)
\end{code}
\end{comment}

\subsubsection{Kinds, Types, Structures and Sequents}
\begin{code}
  data Kind : Set where
    Sol  : Kind -- solid       {⇐, ∙, ⇒}
    Hol  : Kind -- hollow      {⇦, ∘, ⇨}
    Res  : Kind -- reset       {◇, □}
    Ifx  : Kind -- infixation  {⇃, ⇂, ◇↓, □↓}
    Ext  : Kind -- extraction  {↿, ↾, ◇↑, □↑}

  data Type : Set where
    El     : Atom  → Type
    Dia    : Kind  → Type  → Type
    Box    : Kind  → Type  → Type
    UnitR  : Kind  → Type  → Type
    ImpR   : Kind  → Type  → Type  → Type
    ImpL   : Kind  → Type  → Type  → Type

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

  data Sequent : Set where
    _⊢_    : Struct +  → Struct -  → Sequent
    [_]⊢_  : Type      → Struct -  → Sequent
    _⊢[_]  : Struct +  → Type      → Sequent
\end{code}

\begin{code}
  instance
    PolarisedType : Polarised Type
    PolarisedType = record { Pol = Pol′ }
      where
        Pol′ : Type → Polarity
        Pol′ (El    a)      = Pol(a)
        Pol′ (Dia   _ _)    = +
        Pol′ (Box   _ _)    = -
        Pol′ (UnitR _ _)    = +
        Pol′ (ImpR  _ _ _)  = -
        Pol′ (ImpL  _ _ _)  = -
\end{code}

\subsubsection{Type and Structure aliases}
\begin{comment}
\begin{code}
  infix  2 _⊢_ _⊢[_] [_]⊢_
  infixr 3 _∙_ _∘_
  infixl 7 _⇐_ _⇦_
  infixr 7 _⇒_ _⇨_
  infix  7 _⇃_ _⇂_
  infix  7 _↿_ _↾_
  infixr 9 ◇_  □_  ◆_  ■_
  infixr 9 ◇↓_ □↓_ ◆↓_ ■↓_
  infixr 9 ◇↑_ □↑_ ◆↑_ ■↑_
\end{code}
\end{comment}

\begin{multicols}{2}
\begin{code}
  pattern _∙_  x y  = PROD   Sol  x y
  pattern _⇐_  b a  = ImpL   Sol  b a
  pattern _⇒_  a b  = ImpR   Sol  a b
  pattern I         = UNIT   Hol
  pattern Q    a    = UnitR  Hol  a
  pattern _∘_  x y  = PROD   Hol  x y
  pattern _⇨_  a b  = ImpR   Hol  a b
  pattern _⇦_  b a  = ImpL   Hol  b a
  pattern ◇_   a    = Dia    Res  a
  pattern □_   a    = Box    Res  a
  pattern ◆_   x    = DIA    Res  x
  pattern ■_   x    = BOX    Res  x
  pattern ◇↓_  a    = Dia    Ifx  a
  pattern □↓_  a    = Box    Ifx  a
  pattern ◆↓_  x    = DIA    Ifx  x
  pattern ■↓_  x    = BOX    Ifx  x
  pattern _⇃_  a b  = ◇↓ □↓ (a ⇒ b)
  pattern _⇂_  b a  = ◇↓ □↓ (b ⇐ a)
  pattern ◇↑_  a    = Dia    Ext  a
  pattern □↑_  a    = Box    Ext  a
  pattern ◆↑_  x    = DIA    Ext  x
  pattern ■↑_  x    = BOX    Ext  x
  pattern _↿_  a b  = (◇↑ □↑ a) ⇒ b
  pattern _↾_  b a  = b ⇐ (◇↑ □↑ a)
\end{code}
\end{multicols}

\subsubsection{Inference Rules}
\begin{code}
  infix 1 NL_

  data NL_ : Sequent → Set where
    axElR   : ∀ {b}         → Pol(b) ≡ +  → NL · El b · ⊢[ El b ]
    axElL   : ∀ {a}         → Pol(a) ≡ -  → NL [ El a ]⊢ · El a ·
    unfR    : ∀ {x b}       → Pol(b) ≡ -  → NL x ⊢ · b ·  → NL x ⊢[ b ]
    unfL    : ∀ {a y}       → Pol(a) ≡ +  → NL · a · ⊢ y  → NL [ a ]⊢ y
    focR    : ∀ {x b}       → Pol(b) ≡ +  → NL x ⊢[ b ]   → NL x ⊢ · b ·
    focL    : ∀ {a y}       → Pol(a) ≡ -  → NL [ a ]⊢ y   → NL · a · ⊢ y

    impRL   : ∀ {k x y a b} → NL x ⊢[ a ]  → NL [ b ]⊢ y  → NL [ ImpR k a b ]⊢ IMPR k x y
    impRR   : ∀ {k x a b}   → NL x ⊢ IMPR k · a · · b ·   → NL x ⊢ · ImpR k a b ·
    impLL   : ∀ {k x y a b} → NL x ⊢[ a ]  → NL [ b ]⊢ y  → NL [ ImpL k b a ]⊢ IMPL k y x
    impLR   : ∀ {k x a b}   → NL x ⊢ IMPL k · b · · a ·   → NL x ⊢ · ImpL k b a ·
    resRP   : ∀ {k x y z}   → NL y ⊢ IMPR k x z  → NL PROD k x y ⊢ z
    resPR   : ∀ {k x y z}   → NL PROD k x y ⊢ z  → NL y ⊢ IMPR k x z
    resLP   : ∀ {k x y z}   → NL x ⊢ IMPL k z y  → NL PROD k x y ⊢ z
    resPL   : ∀ {k x y z}   → NL PROD k x y ⊢ z  → NL x ⊢ IMPL k z y

    unitRL  : ∀ {k y a}     → NL PROD k · a · (UNIT k) ⊢ y → NL · UnitR k a · ⊢ y
    unitRR  : ∀ {k x b}     → NL x ⊢[  b ]  → NL PROD k x (UNIT k) ⊢[ UnitR k b ]
    unitRI  : ∀ {k x y}     → NL x ⊢   y    → NL PROD k x (UNIT k) ⊢ y

    diaL    : ∀ {k a y}     → NL DIA k · a · ⊢ y  → NL · Dia k a · ⊢ y
    diaR    : ∀ {k x b}     → NL x ⊢[ b ]         → NL DIA k x ⊢[ Dia k b ]
    boxL    : ∀ {k a y}     → NL [ a ]⊢ y         → NL [ Box k a ]⊢ BOX k y
    boxR    : ∀ {k x b}     → NL x ⊢ BOX k · b ·  → NL x ⊢ · Box k b ·
    resBD   : ∀ {k x y}     → NL x ⊢ BOX k y      → NL DIA k x ⊢ y
    resDB   : ∀ {k x y}     → NL DIA k x ⊢ y      → NL x ⊢ BOX k y

    dnB     : ∀ {x y z w}   → NL x ∙ (y ∘ z) ⊢ w        → NL y ∘ ((B ∙ x) ∙ z) ⊢ w
    dnC     : ∀ {x y z w}   → NL (x ∘ y) ∙ z ⊢ w        → NL x ∘ ((C ∙ y) ∙ z) ⊢ w
    upB     : ∀ {x y z w}   → NL y ∘ ((B ∙ x) ∙ z) ⊢ w  → NL x ∙ (y ∘ z) ⊢ w
    upC     : ∀ {x y z w}   → NL x ∘ ((C ∙ y) ∙ z) ⊢ w  → NL (x ∘ y) ∙ z ⊢ w

    ifxRR   : ∀ {x y z w}   → NL ((x ∙ y) ∙ ◆↓ z ⊢ w)  → NL (x ∙ (y ∙ ◆↓ z) ⊢ w)
    ifxLR   : ∀ {x y z w}   → NL ((x ∙ y) ∙ ◆↓ z ⊢ w)  → NL ((x ∙ ◆↓ z) ∙ y ⊢ w)
    ifxLL   : ∀ {x y z w}   → NL (◆↓ z ∙ (y ∙ x) ⊢ w)  → NL ((◆↓ z ∙ y) ∙ x ⊢ w)
    ifxRL   : ∀ {x y z w}   → NL (◆↓ z ∙ (y ∙ x) ⊢ w)  → NL (y ∙ (◆↓ z ∙ x) ⊢ w)

    extRR   : ∀ {x y z w}   → NL (x ∙ (y ∙ ◆↑ z) ⊢ w)  → NL ((x ∙ y) ∙ ◆↑ z ⊢ w)
    extLR   : ∀ {x y z w}   → NL ((x ∙ ◆↑ z) ∙ y ⊢ w)  → NL ((x ∙ y) ∙ ◆↑ z ⊢ w)
    extLL   : ∀ {x y z w}   → NL ((◆↑ z ∙ y) ∙ x ⊢ w)  → NL (◆↑ z ∙ (y ∙ x) ⊢ w)
    extRL   : ∀ {x y z w}   → NL (y ∙ (◆↑ z ∙ x) ⊢ w)  → NL (◆↑ z ∙ (y ∙ x) ⊢ w)

  resRL : ∀ {k x y z} → NL y ⊢ IMPR k x z → NL x ⊢ IMPL k z y
  resRL f = resPL (resRP f)

  resLR : ∀ {k x y z} → NL x ⊢ IMPL k z y → NL y ⊢ IMPR k x z
  resLR f = resPR (resLP f)
\end{code}


\subsubsection{Contexts and Plugging functions}
\begin{code}
  record Pluggable (C I O : Set) : Set where
    field
      _[_] : C → I → O
  open Pluggable {{...}}
\end{code}


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

  instance
    Pluggable-StructI : ∀ {p1 p2} → Pluggable (StructCtxt p1 p2) (Struct p1) (Struct p2)
    Pluggable-StructI = record { _[_] = _[_]′ }
      where
        _[_]′ : ∀ {p1 p2} → StructCtxt p1 p2 → Struct p1 → Struct p2
        ( HOLE          ) [ z ]′ = z
        ( DIA1   k x    ) [ z ]′ = DIA  k    (x [ z ]′)
        ( PROD1  k x y  ) [ z ]′ = PROD k    (x [ z ]′) y
        ( PROD2  k x y  ) [ z ]′ = PROD k x  (y [ z ]′)
        ( BOX1   k x    ) [ z ]′ = BOX  k    (x [ z ]′)
        ( IMPR1  k x y  ) [ z ]′ = IMPR k    (x [ z ]′) y
        ( IMPR2  k x y  ) [ z ]′ = IMPR k x  (y [ z ]′)
        ( IMPL1  k x y  ) [ z ]′ = IMPL k    (x [ z ]′) y
        ( IMPL2  k x y  ) [ z ]′ = IMPL k x  (y [ z ]′)
\end{code}


\begin{multicols}{2}
\begin{code}
  pattern _<∙_  x y  = PROD1   Sol  x y
  pattern _∙>_  x y  = PROD2   Sol  x y
  pattern _<⇐_  y x  = IMPL1   Sol  y x
  pattern _<⇒_  x y  = IMPR2   Sol  x y
  pattern _⇐>_  y x  = IMPL1   Sol  y x
  pattern _⇒>_  x y  = IMPR2   Sol  x y
  pattern _<∘_  x y  = PROD1   Hol  x y
  pattern _∘>_  x y  = PROD2   Hol  x y
  pattern _<⇨_  x y  = IMPR1   Hol  x y
  pattern _<⇦_  y x  = IMPL1   Hol  y x
  pattern _⇨>_  x y  = IMPR2   Hol  x y
  pattern _⇦>_  y x  = IMPL2   Hol  y x
  pattern ◆>_   x    = DIA1    Res  x
  pattern ■>_   x    = BOX1    Res  x
  pattern ◆↓>_  x    = DIA1    Ifx  x
  pattern ■↓>_  x    = BOX1    Ifx  x
  pattern ◆↑>_  x    = DIA1    Ext  x
  pattern ■↑>_  x    = BOX1    Ext  x
\end{code}
\end{multicols}

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

\AgdaFunction{DP} is a type-level function, which takes a sequent
context (a sequent with exactly one hole, either in its antecedent or
in its succedent) and computes the sequent in which the formula in
that hole is displayed (i.e. brought to the top-level).

This is implemented with two potentially mutually recursive functions,
\AgdaFunction{DPL} and \AgdaFunction{DPR}, which manipulate the
antecedent and succedent. By splitting up the sequent in two
arguments---the antecedent and the succedent---these functions become
structurally recursive.

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

\noindent
\AgdaFunction{dp} is a term-level function, which takes a sequent
context $s$ (as  above), a structure $w$, and a proof for the sequent $s [ w
]$. It then computes an isomorphism between proofs of $s [ w ]$ and
proofs of $\AgdaFunction{DP}(s)[ w ]$ where, in the second proof, the formula $w$ is
guaranteed  to be displayed.

\begin{code}
  mutual
    dp : ∀ {p} (s : SequentCtxt p) (w : Struct p) → (NL s [ w ]) ⇔ (NL DP(s)[ w ])
    dp (x <⊢ y) w = dpL x y w
    dp (x ⊢> y) w = dpR x y w

    dpL  : ∀ {p} (x : StructCtxt p +) (y : Struct -) (w : Struct p)
         → (NL x [ w ] ⊢ y) ⇔ (NL DPL x y [ w ])
    dpL ( HOLE          )  z w = I.id
    dpL ( DIA1   k x    )  z w = dpL x  ( BOX   k z    )  w I.∘ mkISO resDB resBD
    dpL ( PROD1  k x y  )  z w = dpL x  ( IMPL  k z y  )  w I.∘ mkISO resPL resLP
    dpL ( PROD2  k x y  )  z w = dpL y  ( IMPR  k x z  )  w I.∘ mkISO resPR resRP

    dpR  : ∀ {p} (x : Struct +) (y : StructCtxt p -) (w : Struct p)
         → (NL x ⊢ y [ w ]) ⇔ (NL DPR x y [ w ])
    dpR x ( HOLE          ) w = I.id
    dpR x ( BOX1   k y    ) w = dpR    ( DIA   k x    ) y  w I.∘ mkISO resBD resDB
    dpR x ( IMPR1  k y z  ) w = dpL y  ( IMPL  k z x  )    w I.∘ mkISO resRL resLR
    dpR x ( IMPR2  k y z  ) w = dpR    ( PROD  k y x  ) z  w I.∘ mkISO resRP resPR
    dpR x ( IMPL1  k z y  ) w = dpR    ( PROD  k x y  ) z  w I.∘ mkISO resLP resPL
    dpR x ( IMPL2  k z y  ) w = dpL y  ( IMPR  k x z  )    w I.∘ mkISO resLR resRL
\end{code}

\noindent
\AgdaFunction{dp1} and \AgdaFunction{dp2} are helper functions, which
allow you to access the two sides of the isomorphism more easily.\\

\begin{code}
  dp1 : ∀ {p} (s : SequentCtxt p) (w : Struct p) → NL s [ w ] → NL DP(s)[ w ]
  dp1 s w f = to (dp s w) ⟨$⟩ f

  dp2 : ∀ {p} (s : SequentCtxt p) (w : Struct p) → NL DP(s)[ w ] → NL s [ w ]
  dp2 s w f = from (dp s w) ⟨$⟩ f
\end{code}


\subsubsection{Structuralising Types}
Because each logical connective has a structural equivalent, it is
possible---to a certain extend---structuralise logical connectives
en masse. The function \AgdaFunction{St} takes a type, and computes
the maximally structuralised version of that type, given a target
polarity $p$.

\begin{code}
  St : ∀ {p} → Type → Struct p
  St { p = + } ( Dia    k  a   )  = DIA   k (St a)
  St { p = - } ( Box    k  a   )  = BOX   k (St a)
  St { p = + } ( UnitR  k  a   )  = PROD  k (St a) (UNIT k)
  St { p = - } ( ImpR   k  a b )  = IMPR  k (St a) (St b)
  St { p = - } ( ImpL   k  b a )  = IMPL  k (St b) (St a)
  St { p = _ } a                  = · a ·
\end{code}

\noindent
We know that if we try to structuralise a positive type as a negative
structure, or vice versa, it results in the primitive structure. The
lemmas \AgdaFunction{lem-Neg-St} and \AgdaFunction{lem-Pos-St} encode
this knowledge.

\begin{code}
  lem-Neg-St : ∀ a → Pol(a) ≡ - → St { + } a ≡ · a ·
  lem-Neg-St ( El        a    ) n = refl
  lem-Neg-St ( Dia    k  a    ) ()
  lem-Neg-St ( Box    k  a    ) n = refl
  lem-Neg-St ( UnitR  k  a    ) ()
  lem-Neg-St ( ImpR   k  a b  ) n = refl
  lem-Neg-St ( ImpL   k  b a  ) n = refl

  lem-Pos-St : ∀ a → Pol(a) ≡ + → St { - } a ≡ · a ·
  lem-Pos-St ( El        a    ) p = refl
  lem-Pos-St ( Dia    k  a    ) p = refl
  lem-Pos-St ( Box    k  a    ) ()
  lem-Pos-St ( UnitR  k  a    ) p = refl
  lem-Pos-St ( ImpR   k  a b  ) ()
  lem-Pos-St ( ImpL   k  b a  ) ()
\end{code}

\noindent
The functions \AgdaFunction{stL}, \AgdaFunction{stR} and
\AgdaFunction{st} actually perform the structuralisation described by
\AgdaFunction{St}. Given a proof for a sequent $s$, they will
structuralise either the antecedent, the succedent, or both.

\begin{code}
  mutual
    st : ∀ {a b} → NL St a ⊢ St b → NL · a · ⊢ · b ·
    st f = stL (stR f)

    stL : ∀ {a y} → NL St a ⊢ y → NL · a · ⊢ y
    stL { a = El        a    } f = f
    stL { a = Dia    k  a    } f = diaL (resBD (stL (resDB f)))
    stL { a = Box    k  a    } f = f
    stL { a = UnitR  k  a    } f = unitRL (resLP (stL (resPL f)))
    stL { a = ImpR   k  a b  } f = f
    stL { a = ImpL   k  b a  } f = f

    stR : ∀ {x b} → NL x ⊢ St b → NL x ⊢ · b ·
    stR { b = El        a    } f = f
    stR { b = Dia    k  a    } f = f
    stR { b = Box    k  a    } f = boxR (resDB (stR (resBD f)))
    stR { b = UnitR  k  a    } f = f
    stR { b = ImpR   k  a b  } f = impRR (resPR (stR (resLP (stL (resPL (resRP f))))))
    stR { b = ImpL   k  b a  } f = impLR (resPL (stR (resRP (stL (resPR (resLP f))))))
\end{code}

\subsubsection{Identity Expansion}
\begin{code}
  mutual
    ax : ∀ {a} → NL · a · ⊢ · a ·
    ax {a} with Pol(a) | inspect Pol(a)
    ... | + | P.[ p ]  rewrite lem-Pos-St  a p  = stL (focR p (axR′ p))
    ... | - | P.[ n ]  rewrite lem-Neg-St  a n  = stR (focL n (axL′ n))

    axR : ∀ {b} → NL St b ⊢[ b ]
    axR {b} with Pol(b) | inspect Pol(b)
    ... | + | P.[ p ]                           = axR′ p
    ... | - | P.[ n ]  rewrite lem-Neg-St  b n  = unfR n (stR (focL n (axL′ n)))

    axL : ∀ {a} → NL [ a ]⊢ St a
    axL {a} with Pol(a) | inspect Pol(a)
    ... | + | P.[ p ]  rewrite lem-Pos-St  a p  = unfL p (stL (focR p (axR′ p)))
    ... | - | P.[ n ]                           = axL′ n

    axR′ : ∀ {b} → Pol(b) ≡ + → NL St b ⊢[ b ]
    axR′ { b = El        a    } p = axElR p
    axR′ { b = Dia    k  a    } p = diaR axR
    axR′ { b = Box    k  a    } ()
    axR′ { b = UnitR  k  a    } p = unitRR axR
    axR′ { b = ImpR   k  a b  } ()
    axR′ { b = ImpL   k  b a  } ()

    axL′ : ∀ {a} → Pol(a) ≡ - → NL [ a ]⊢ St a
    axL′ { a = El        a    } n = axElL n
    axL′ { a = Dia    k  a    } ()
    axL′ { a = Box    k  a    } n = boxL axL
    axL′ { a = UnitR  k  a    } ()
    axL′ { a = ImpR   k  a b  } n = impRL axR axL
    axL′ { a = ImpL   k  b a  } n = impLL axR axL
\end{code}

\subsection{Quanfitier Raising}
\begin{code}
  data QRCtxt : Set where
    HOLE   : QRCtxt
    PROD1  : QRCtxt    → Struct +  → QRCtxt
    PROD2  : Struct +  → QRCtxt    → QRCtxt

  instance
    Pluggable-QR : Pluggable QRCtxt (Struct +) (Struct +)
    Pluggable-QR = record { _[_] = _[_]′ }
      where
        _[_]′ : QRCtxt → Struct + → Struct +
        ( HOLE        ) [ z ]′ = z
        ( PROD1  x y  ) [ z ]′ = PROD Sol    (x [ z ]′) y
        ( PROD2  x y  ) [ z ]′ = PROD Sol x  (y [ z ]′)
\end{code}

\begin{code}
  trace : QRCtxt → Struct +
  trace ( HOLE        )  = UNIT Hol
  trace ( PROD1  x y  )  = PROD Sol (PROD Sol C (trace x)) y
  trace ( PROD2  x y  )  = PROD Sol (PROD Sol B x) (trace y)
\end{code}

\begin{code}
  ↑ : ∀ x {a z} → NL · a · ∘ trace(x) ⊢ z → NL x [ · Q a · ] ⊢ z
  ↑ x f = init x (move x f)
    where
    init : ∀ (x : QRCtxt) {a z} → NL x [ · a · ∘ I ] ⊢ z → NL x [ · Q a · ] ⊢ z
    init ( HOLE        ) f = unitRL f
    init ( PROD1  x y  ) f = resLP (init x (resPL f))
    init ( PROD2  x y  ) f = resRP (init y (resPR f))
    move : ∀ (x : QRCtxt) {y z} → NL y ∘ trace(x) ⊢ z → NL x [ y ∘ I ] ⊢ z
    move ( HOLE        ) f = f
    move ( PROD1  x y  ) f = resLP (move x (resPL (upC f)))
    move ( PROD2  x y  ) f = resRP (move y (resPR (upB f)))

  ↓ : ∀ x {y z} → NL x [ y ] ⊢ z → NL y ∘ trace(x) ⊢ z
  ↓ ( HOLE        ) f = unitRI f
  ↓ ( PROD1  x y  ) f = dnC (resLP (↓ x (resPL f)))
  ↓ ( PROD2  x y  ) f = dnB (resRP (↓ y (resPR f)))
\end{code}

\begin{code}
  q↑ : ∀ x {y b c} → NL trace(x) ⊢[ b ] → NL [ c ]⊢ y → NL x [ · Q (c ⇦ b) · ] ⊢ y
  q↑ x f g = ↑ x (resLP (focL refl (impLL f g)))

  q↓ : ∀ x {a b} → NL x [ · a · ] ⊢ · b · → NL trace(x) ⊢ · a ⇨ b ·
  q↓ x f = impRR (resPR (↓ x f))
\end{code}



\subsection{Interpretation in Agda}
\begin{code}
module InterpretationInAgda
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
  open module NL = Syntax Atom PolarisedAtom hiding (_∘_)
\end{code}
\end{comment}

\begin{code}
  instance
    TranslateType : Translate NL.Type Set
    TranslateType = record { _* = _*′ }
      where
        _*′ : NL.Type → Set
        El        a    *′ = a *
        Dia    _  a    *′ = a *′
        Box    _  a    *′ = a *′
        UnitR  _  a    *′ = a *′
        ImpR   _  a b  *′ = a *′ → b *′
        ImpL   _  b a  *′ = a *′ → b *′

    TranslateStruct : ∀ {p} → Translate (NL.Struct p) Set
    TranslateStruct = record { _* = _*′ }
      where
        _*′ : ∀ {p} → NL.Struct p → Set
        · a ·         *′ = a *
        B             *′ = ⊤
        C             *′ = ⊤
        DIA   _  x    *′ = x *′
        UNIT  _       *′ = ⊤
        PROD  _  x y  *′ = x *′ × y *′
        BOX   _  x    *′ = x *′
        IMPR  _  x y  *′ = x *′ → y *′
        IMPL  _  y x  *′ = x *′ → y *′

    TranslateSequent : Translate NL.Sequent Set
    TranslateSequent = record { _* = _*′ }
      where
        _*′ : NL.Sequent → Set
        ( x ⊢ y     )*′ = x * → y *
        ( [ a ]⊢ y  )*′ = a * → y *
        ( x ⊢[ b ]  )*′ = x * → b *
\end{code}

\begin{code}
  instance
    TranslateProof : ∀ {s} → Translate (NL s) (s *)
    TranslateProof = record { _* = _*′ }
      where
        _*′ : ∀ {s} → NL s → s *
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
        unitRL  f    *′ = λ{  x       → (f *′) (x , _)  }
        unitRR  f    *′ = λ{ (x , _)  → (f *′)  x       }
        unitRI  f    *′ = λ{ (x , _)  → (f *′)  x       }
        diaL    f    *′ = f *′
        diaR    f    *′ = f *′
        boxL    f    *′ = f *′
        boxR    f    *′ = f *′
        resBD   f    *′ = f *′
        resDB   f    *′ = f *′
        dnB     f    *′ = λ{ ( y , (_ , x) , z)  → (f *′) ( x , y  , z) }
        dnC     f    *′ = λ{ ( x , (_ , y) , z)  → (f *′) ((x , y) , z) }
        upB     f    *′ = λ{ ( x , y   , z)  → (f *′) ( y , (_ , x) , z) }
        upC     f    *′ = λ{ ((x , y)  , z)  → (f *′) ( x , (_ , y) , z) }
        ifxRR   f    *′ = λ{ ( x , y   , z)  → (f *′) ((x , y) , z)  }
        ifxLR   f    *′ = λ{ ((x , z)  , y)  → (f *′) ((x , y) , z)  }
        ifxLL   f    *′ = λ{ ((z , y)  , x)  → (f *′) ( z , y  , x)  }
        ifxRL   f    *′ = λ{ ( y , z   , x)  → (f *′) ( z , y  , x)  }
        extRR   f    *′ = λ{ ((x , y)  , z)  → (f *′) ( x , y  , z)  }
        extLR   f    *′ = λ{ ((x , y)  , z)  → (f *′) ((x , z) , y)  }
        extLL   f    *′ = λ{ ( z , y   , x)  → (f *′) ((z , y) , x)  }
        extRL   f    *′ = λ{ ( z , y   , x)  → (f *′) ( y , z  , x)  }
\end{code}

\end{appendices}
\end{document}
