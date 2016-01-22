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
%format :←       = "\slash"
%format :→       = "\backslash"
%format :⇃       = "\downharpoonleft"
%format :⇂       = "\downharpoonright"
%format :⇨       = "\fatbslash"
%format :&       = "\mathbin{\&}"
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

\appendix
\renewcommand{\thesection}{B}
\section{Formalisation of NLQ in Haskell}

\begin{comment}

> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE QuasiQuotes #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE TemplateHaskell #-}
> {-# LANGUAGE NoImplicitPrelude #-}

\end{comment}

> import NLIBC.Prelude

\subsection{The Lexicon}

\begin{lstlisting}
  lex :: (SingI a) => Name -> Word a
\end{lstlisting}

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

\begin{lstlisting}
  lex_ :: (SingI a) => Hask (H a) -> Word a
\end{lstlisting}

> a, some, every :: Word (Q NP S S :← N)
> a         = some
> some      = lex_ (\f g -> exists E (\x -> f x ∧ g x))
> every     = lex_ (\f g -> forall E (\x -> f x ⊃ g x))

> someone, everyone :: Word (Q NP S S)
> someone   = some  <$ person
> everyone  = every <$ person

> to        = lex_ (\x -> x)  :: Word (INF :← IV)
> of_       = lex  "of"       :: Word ((N :→ N) :← NP)
> the       = lex  "the"      :: Word (NP :← N)

> want     :: Word ((IV :← INF) :& ((IV :← INF) :← NP))
> want      = lex_ (want1 , want2)
>   where
>   wantP         = "want" ∷ TET
>   want1    f x  = wantP (f x) x
>   want2 y  f x  = wantP (f y) x
> wants     = want

> same, different :: Word (Q (Q A (NP :⇨ S) (NP :⇨ S)) S S)
> same      = lex_ same'
>   where
>   same' k = exists E (\z -> k (\k' x -> k' (\f y -> f y :∧ y ≡ z) x))
> different = lex_ diff1
>   where
>   diff1 k = exists EET (\f -> diff2 f ∧ k (\k x -> k (\g y -> g y ∧ f x y) x))
>   diff2 f = forall E   (\x -> forall E (\y -> not (exists E (\z -> f z x ∧ f z y))))


> type WHICH1 = Q NP NP ((N :→ N) :← (NP :⇃ S))
> type WHICH2 = Q NP NP ((N :→ N) :← (S :⇂ NP))
>
> which :: Word (WHICH1 :& WHICH2)
> which = lex_ (which' , which')
>   where
>     which' f g h x = h x ∧ (g (f x))

> type WHO1 = (Q NP S S) :← (NP :⇃ S)
> type WHO2 = (Q NP S S) :← (S :⇂ NP)
>
> who :: Word (WHO1 :& WHO2)
> who = lex_ (who' , who')
>   where
>     who' f g = exists E (\x -> g x ∧ f x)

> notEmpty :: (Expr E -> Expr T)  -> Expr T
> notEmpty f = exists E (\x -> f x)
>
> moreThanOne :: (Expr E -> Expr T)  -> Expr T
> moreThanOne f = exists E (\x -> exists E (\y -> f x ∧ f y ∧ x ≢ y))
>
> plural :: Word (NS :← N)
> plural = lex_
>   (\f g -> exists ET (\h -> moreThanOne h ∧ forall E (\x -> h x ⊃ (f x ∧ g x))))


\subsection{Examples}

> s0  = [nlq| john runs |]

\begin{lstlisting}\perform{s0}\end{lstlisting}

> s1  = [nlq| john    likes mary     |]

\begin{lstlisting}\perform{s1}\end{lstlisting}

> s2  = [nlq| someone likes mary     |]

\begin{lstlisting}\perform{s2}\end{lstlisting}

> s3  = [nlq| john    likes everyone |]

\begin{lstlisting}\perform{s3}\end{lstlisting}

> s4  = [nlq| someone likes everyone |]

\begin{lstlisting}\perform{s4}\end{lstlisting}

> s5  = [nlq| (the           waiter) serves everyone |]

\begin{lstlisting}\perform{s5}\end{lstlisting}

> s6  = [nlq| (the same      waiter) serves everyone |]

\begin{lstlisting}\perform{s6}\end{lstlisting}

> s7  = [nlq| (a   different waiter) serves everyone |]

\begin{lstlisting}\perform{s7}\end{lstlisting}

> s8  = [nlq| mary  wants           to leave |]

\begin{lstlisting}\perform{s8}\end{lstlisting}

> s9  = [nlq| mary (wants john)     to leave |]

\begin{lstlisting}\perform{s9}\end{lstlisting}

> s10 = [nlq| mary (wants everyone) to leave |]

\begin{lstlisting}\perform{s10}\end{lstlisting}

> s11 = [nlq| mary  wants           to like bill |]

\begin{lstlisting}\perform{s11}\end{lstlisting}

> s12 = [nlq| mary (wants john)     to like bill |]

\begin{lstlisting}\perform{s12}\end{lstlisting}

> s13 = [nlq| mary (wants everyone) to like bill |]

\begin{lstlisting}\perform{s13}\end{lstlisting}

> s14 = [nlq| mary  wants           to like someone |]

\begin{lstlisting}\perform{s14}\end{lstlisting}

> s15 = [nlq| mary (wants john)     to like someone |]

\begin{lstlisting}\perform{s15}\end{lstlisting}

> s16 = [nlq| mary (wants everyone) to like someone |]

\begin{lstlisting}\perform{s16}\end{lstlisting}

> s17 = [nlq| mary says <john     likes bill> |]

\begin{lstlisting}\perform{s17}\end{lstlisting}

> s18 = [nlq| mary says <everyone likes bill> |]

\begin{lstlisting}\perform{s18}\end{lstlisting}

> s19 = [nlq| mary reads a book                which  john likes |]

\begin{lstlisting}\perform{s19}\end{lstlisting}

> s20 = [nlq| mary reads a book (the author of which) john likes |]

\begin{lstlisting}\perform{s20}\end{lstlisting}

> s21 = [nlq| mary sees foxes   |]

\begin{lstlisting}\perform{s21}\end{lstlisting}

> s22 = [nlq| mary sees the fox |]

\begin{lstlisting}\perform{s22}\end{lstlisting}

> s23 = [nlq| mary sees a   fox |]

\begin{lstlisting}\perform{s23}\end{lstlisting}

> s24 = [nlq| alice reads a book (the author of which) fears the ocean |]

\begin{lstlisting}\perform{s24}\end{lstlisting}

> s25 = [nlq| alice knows who leaves |]

\begin{lstlisting}\perform{s25}\end{lstlisting}

\end{appendices}
\end{document}
