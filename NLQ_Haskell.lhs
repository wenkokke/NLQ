\documentclass{article}

%include lhs2TeX.fmt
%options ghci -idata -fobject-code

%format E        = "\mathbf{e}"
%format T        = "\mathbf{t}"
%format ET       = E T
%format EET      = E ET
%format TET      = T ET
%format TT       = T T
%format TTT      = T TT
%format ET_T     = "(" ET ")" T
%format forall x = "\forall_{" x "}"
%format exists x = "\exists_{" x "}"
%format of       = "\mathit{of}"
%format of_      = "\mathit{of}"
%format <$       = "\triangleleft"
%format $>       = "\triangleright"
%format ∷        = ::
%format :->      = ":\rightarrow"
%format :←       = "\slash"
%format :→       = "\backslash"
%format :⇃       = "\downharpoonleft"
%format :⇂       = "\downharpoonright"
%format :⇨       = "\fatbslash"
%format :&       = "\mathbin{\&}"
%format ∧        = "\mathbin{\wedge}"
%format ⊃        = "\mathbin{\supset}"
%format Res      = "\Diamond\!\!"
%format Q a b c  = "\mathbf{Q}(" c "\!\!\fatslash" "(" a "\fatbslash" b ")" ")"

\usepackage{appendix}
\usepackage{stmaryrd}
\setlength{\mathindent}{0cm}
%\usepackage[utf8]{inputenc}
%\usepackage{newunicodechar}
%\newunicodechar{∃}{\ensuremath{\exists}}
%\newunicodechar{∄}{\ensuremath{\nexists}}
%\newunicodechar{∀}{\ensuremath{\forall}}
%\newunicodechar{∧}{\ensuremath{\wedge}}
%\newunicodechar{⊃}{\ensuremath{\supset}}
%\newunicodechar{λ}{\ensuremath{\lambda}}
%\newunicodechar{≡}{\ensuremath{\equiv}}
%\newunicodechar{≢}{\ensuremath{\not\equiv}}
%\newunicodechar{¬}{\ensuremath{\neg}}
\usepackage{comment}
\usepackage{listings}
\lstset{
  frame=leftline,
  basicstyle=\ttfamily\small,
  breaklines=true,
  breakatwhitespace=true,
  inputencoding=utf8,
  extendedchars=true,
  literate=
   {∃}{{\ensuremath{\exists}}}1
   {∄}{{\ensuremath{\nexists}}}1
   {∀}{{\ensuremath{\forall}}}1
   {∧}{{\ensuremath{\wedge}}}1
   {⊃}{{\ensuremath{\supset}}}1
   {λ}{{\ensuremath{\lambda}}}1
   {≡}{{\ensuremath{\equiv}}}1
   {≢}{{\ensuremath{\not\equiv}}}1
   {¬}{{\ensuremath{\neg}}}1,
}

\begin{document}
\begin{appendices}

\begin{comment}

> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE QuasiQuotes #-}
> {-# LANGUAGE TemplateHaskell #-}
> {-# LANGUAGE NoImplicitPrelude #-}

\end{comment}

\appendix
\renewcommand{\thesection}{B}
\section{Formalisation of NLQ in Haskell}

In this appendix, we will discuss the Haskell `formalisation` of
NLQ. Now, formalisation is a bit of an overstatement when talking
about Haskell, since the Haskell type-system itself is unsound, as the
language allows non-termination. However, in modern Haskell, using the
singletons library, it is quite possible to do verification.

The reason that we have implemented a Haskell version as well as an
Agda version of NLQ, is because while Agda excels at verification, it
is quite a slow language, and we want to do proof search. The Haskell
version, on the other hand, has very good performance when it comes to
proof search. However, writing proofs in Haskell is tedious, and in
some instances (mostly when contexts are used) the Haskell version of
an Agda proof will require the use of |unsafeCoerce|---though all
instances of |unsafeCoerce| can be removed when |InjectiveTypeFamilies|
are released.

Because the two implementations are so similar, and because discussing
a proof search algorithm is rather boring, in what follows we will
\emph{only} discuss the interface to NLQ---whatever you need to write
your own examples. The first step in this, is to import the NLQ
prelude.
\\

> import NLQ.Prelude

\\
Once we've done this, we can start the lexicon.


\subsection{The Lexicon}

The main function to construct lexical entries, is the function |lex|,
which has the following type:
\begin{lstlisting}
  lex :: (SingI a) => Name -> Word a
\end{lstlisting}
That is to say, it takes a |Name|---which is just a string---and
returns a |Word| of type |a|.\footnote{%
  The |SingI| typeclass is the class of types which have a singleton
  associated with them---a term-level representation of a type, or a
  type-level representation for a term, depending on your
  perspective. All syntactic types have singleton instances associated
  with them.
}
However, since the type |a| only occurs in the result-type, it
important to always explicitly write the type. For instance, below we
define a small lexicon of proper nouns, verbs and nouns:
\\

> john, mary, bill, alice :: Word NP
> john      = lex "john"
> mary      = lex "mary"
> bill      = lex "bill"
> alice     = lex "alice"
>
> run, leave :: Word IV
> run       = lex "run"     ;  runs    = run
> leave     = lex "leave"   ;  leaves  = leave
>
> read, see, like, serve, fear, know :: Word TV
> read      = lex "read"    ;  reads   = read
> see       = lex "see"     ;  sees    = see
> like      = lex "like"    ;  likes   = like
> serve     = lex "serve"   ;  serves  = serve
> fear      = lex "fear"    ;  fears   = fear
> know      = lex "know"    ;  knows   = know
>
> say :: Word (IV :← Res S)
> say       = lex "say"     ; says     = say
>
> person, waiter, fox, book, author, ocean :: Word N
> person    = lex "person"  ; people   = plural <$ person
> waiter    = lex "waiter"  ; waiters  = plural <$ waiter
> fox       = lex "fox"     ; foxes    = plural <$ fox
> book      = lex "book"    ; books    = plural <$ book
> author    = lex "author"  ; authors  = plural <$ author
> ocean     = lex "ocean"   ; oceans   = plural <$ ocean

\\
If you ever get an error like the error given below, you have probably
forgotten to give an explicit type for a lexicon entry:
\begin{lstlisting}
  NLQ_Haskell.lhs:134:15:
    No instance for (Data.Singletons.SingI a0)
      arising from a use of ‘lex’
    The type variable ‘a0’ is ambiguous
    ...
    In the expression: lex "alice"
    In an equation for ‘alice’: alice = lex "alice"
\end{lstlisting}
At this point, it is best to ignore the plural definitions, they will
make sense soon enough.

\vspace*{1\baselineskip}

Most \emph{interesting} lexical entries are given as \emph{terms}
instead of simply as postulates. For this, there is the function
|lex_|, which has the following type:
\begin{lstlisting}
  lex_ :: (SingI a) => Hask (H a) -> Word a
\end{lstlisting}
In this type, the type family |H| is the function which translates
syntactic types to semantic types, and the type family |Hask| is a
type family which translates a semantic type to a Haskell
type, prefixing all atomic types with the datatype |Expr|.
Therefore, if you write, e.g.\ a lexical entry of type |N| using
|lex_|, you will be expected to provide something of type |Expr E ->
Expr T|:
\\

> a, some, every :: Word (Q NP S S :← N)
> a         = some
> some      = lex_ (\f g -> exists E (\x -> f x ∧ g x))
> every     = lex_ (\f g -> forall E (\x -> f x ⊃ g x))

\\
The functions |forall E|, |exists E|, |∧| and |⊃| are defined in
|NLQ.Prelude|.

Now that we have definitions for |some|, |every|, and |person| it
would be a shame if we could not simply give the definitions by
applying the one to the other. However, since words are directionally
typed, we cannot use Haskell's function application. Instead,
|NLQ.Prelude| provides you with two directional versions of
application, written |<$| and |$>|:
\\

> someone, everyone :: Word (Q NP S S)
> someone   = some  <$ person
> everyone  = every <$ person

\\
This was the same |<$| that was used in the definitions of the plural
nouns above. In fact, |plural| is simply a word---albeit a somewhat
complex one:
\\

> moreThanOne :: (Expr E -> Expr T)  -> Expr T
> moreThanOne f = exists E (\x -> exists E (\y -> f x ∧ f y ∧ x ≢ y))
>
> plural :: Word (NS :← N)
> plural = lex_
>   (\f g -> exists ET (\h -> moreThanOne h ∧ forall E (\x -> h x ⊃ (f x ∧ g x))))

\\
Note that the definition of |plural| uses an existential quantifying
over \emph{predicates}. In fact, our semantic calculus is a
higher-order logic, so |forall x| and |exists x| take an extra
argument to determine which type they quantify over.
This type has to be provided using a singleton. There are a number of
predefined singletons for semantic types, amongst which are |E|, |T|,
|ET|, |EET|, |TET|, |TT|, |TTT| and |ET_T|, but if you need to form
your own, you can use |:->| to create function types.

Right, let's carry on, and define some simple function words. Note
that we are defining |the| as a postulate, since we do not really want
to commit to an implementation yet---though if we would want to, it
could easily be implemented it using quantification:
\\

> to        = lex_ (\x -> x)  :: Word (INF :← IV)
> of_       = lex  "of"       :: Word ((N :→ N) :← NP)
> the       = lex  "the"      :: Word (NP :← N)

\\
Next up, |want|. As discussed, |want| has an ambiguous type:
it can take either an NP object, a VP object or both! For these
examples, we will only use the last two of these meanings:
\\

> want     :: Word ((IV :← INF) :& ((IV :← INF) :← NP))
> want      = lex_ ((want2 , want3))
>   where
>   want2    f x  = ("want" ∷ TET) (f  x)  x
>   want3 y  f x  = ("want" ∷ TET) (f  y)  x
> wants     = want

\\
Note that in the definition of |want|, we had to have a postulate
want, which we called |want|. For this, we have the |∷|-operator. This
operator takes a string and the singleton for a semantic type |a|, and
returns an expression of type |Hask a|.

Next, we define the double/parasitic quantifiers |same| and
|different|. Note that the function |≡| used in these definitions is
predefined, as is its negation:
\\

> same, different :: Word (Q (Q A (NP :⇨ S) (NP :⇨ S)) S S)
> same      = lex_ same'
>   where
>   same' k = exists E (\z -> k (\k' x -> k' (\f y -> f y :∧ y ≡ z) x))
> different = lex_ diff1
>   where
>   diff1 k = exists EET (\f -> diff2 f ∧ k (\k x -> k (\g y -> g y ∧ f x y) x))
>   diff2 f = forall E   (\x -> forall E (\y -> not (exists E (\z -> f z x ∧ f z y))))

\\
Lastly, we define |which|. As an example of the fact that is is plain
Haskell, we use |type|-declarations to split up the type for |which|
in its two possible types, i.e.\ whether its going to insert its
clause into a right or a left gap. The semantics, however, stay the
same:

> type WHICH1 = Q NP NP ((N :→ N) :← (NP :⇃ S))
> type WHICH2 = Q NP NP ((N :→ N) :← (S :⇂ NP))
>
> which :: Word (WHICH1 :& WHICH2)
> which = lex_ (which' , which')
>   where
>     which' f g h x = h x ∧ (g (f x))

\\
And with the lexicon over with, we can start writing examples!

\subsection{Examples}

In this section, we will treat a number of examples. There are some
things that need explaining.

First, the quasiquoter |nlq|. This is not a terribly interesting
function, as it does none of the parsing. What it does is take a parse
tree, turn it into a tree of Haskell pairs, and feed it to the actual
parser, |parseBwd|.
For instance, in the first example, ``john runs'' is taken, and turned
into the Haskell expression |parseBwd S (john,runs)|. The input string
is taken as a right-branching parse tree, so any left branches have to
be explicitly written. In addition, any scope islands can be written
as |<...>|.

Secondly, with some lhs2\TeX\ magic, I have inserted the results of
the examples in listings below them. These listings list the precise
output of the Haskell program.
What follows is a list of examples, and their interpretations:
\\

> s0  = [nlq| john runs |]

\begin{lstlisting} \perform{s0} \end{lstlisting}

> s1  = [nlq| john    likes mary     |]

\begin{lstlisting} \perform{s1} \end{lstlisting}

> s2  = [nlq| someone likes mary     |]

\begin{lstlisting} \perform{s2} \end{lstlisting}

> s3  = [nlq| john    likes everyone |]

\begin{lstlisting} \perform{s3} \end{lstlisting}

> s4  = [nlq| someone likes everyone |]

\begin{lstlisting} \perform{s4} \end{lstlisting}

> s5  = [nlq| (the           waiter) serves everyone |]

\begin{lstlisting} \perform{s5} \end{lstlisting}

> s6  = [nlq| (the same      waiter) serves everyone |]

\begin{lstlisting} \perform{s6} \end{lstlisting}

> s7  = [nlq| (a   different waiter) serves everyone |]

\begin{lstlisting} \perform{s7} \end{lstlisting}

> s8  = [nlq| mary  wants           to leave |]

\begin{lstlisting} \perform{s8} \end{lstlisting}

> s9  = [nlq| mary (wants john)     to leave |]

\begin{lstlisting} \perform{s9} \end{lstlisting}

> s10 = [nlq| mary (wants everyone) to leave |]

\begin{lstlisting} \perform{s10} \end{lstlisting}

> s11 = [nlq| mary  wants           to like bill |]

\begin{lstlisting} \perform{s11} \end{lstlisting}

> s12 = [nlq| mary (wants john)     to like bill |]

\begin{lstlisting} \perform{s12} \end{lstlisting}

> s13 = [nlq| mary (wants everyone) to like bill |]

\begin{lstlisting} \perform{s13} \end{lstlisting}

> s14 = [nlq| mary  wants           to like someone |]

\begin{lstlisting} \perform{s14} \end{lstlisting}

> s15 = [nlq| mary (wants john)     to like someone |]

\begin{lstlisting} \perform{s15} \end{lstlisting}

> s16 = [nlq| mary (wants everyone) to like someone |]

\begin{lstlisting} \perform{s16} \end{lstlisting}

> s17 = [nlq| mary says <john     likes bill> |]

\begin{lstlisting} \perform{s17} \end{lstlisting}

> s18 = [nlq| mary says <everyone likes bill> |]

\begin{lstlisting} \perform{s18} \end{lstlisting}

> s19 = [nlq| mary reads a book                which  john likes |]

\begin{lstlisting} \perform{s19} \end{lstlisting}

> s20 = [nlq| mary reads a book (the author of which) john likes |]

\begin{lstlisting} \perform{s20} \end{lstlisting}

> s21 = [nlq| mary sees foxes   |]

\begin{lstlisting} \perform{s21} \end{lstlisting}

> s22 = [nlq| mary sees the fox |]

\begin{lstlisting} \perform{s22} \end{lstlisting}

> s23 = [nlq| mary sees a   fox |]

\begin{lstlisting} \perform{s23} \end{lstlisting}

> s24 = [nlq| alice reads a book (the author of which) fears the ocean |]

\begin{lstlisting} \perform{s24} \end{lstlisting}

\end{appendices}
\end{document}
