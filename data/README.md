> {-# LANGUAGE GADTs                  #-}
> {-# LANGUAGE DataKinds              #-}
> {-# LANGUAGE RankNTypes             #-}
> {-# LANGUAGE QuasiQuotes            #-}
> {-# LANGUAGE TypeOperators          #-}
> {-# LANGUAGE KindSignatures         #-}
> {-# LANGUAGE TemplateHaskell        #-}
> {-# LANGUAGE PatternSynonyms        #-}
> {-# LANGUAGE FlexibleContexts       #-}
> {-# LANGUAGE FlexibleInstances      #-}
> {-# LANGUAGE NoImplicitPrelude      #-}
> {-# LANGUAGE UndecidableInstances   #-}
> {-# LANGUAGE MultiParamTypeClasses  #-}
> {-# LANGUAGE FunctionalDependencies #-}
> module Main where

> import NLIBC.Prelude

Examples -- Backward-Chaining Search
====================================

> bwd0  = [bwd| john runs |]
> bwd1  = [bwd| john    likes mary     |]
> bwd2  = [bwd| someone likes mary     |]
> bwd3  = [bwd| john    likes everyone |]
> bwd4  = [bwd| someone likes everyone |]
> bwd5  = [bwd| (the           waiter) serves everyone |]
> bwd6  = [bwd| (the same      waiter) serves everyone |]
> bwd7  = [bwd| (a   different waiter) serves everyone |]
> bwd8  = [bwd| mary  wants           to leave |]
> bwd9  = [bwd| mary (wants john)     to leave |]
> bwd10 = [bwd| mary (wants everyone) to leave |]
> bwd11 = [bwd| mary  wants           to like bill |]
> bwd12 = [bwd| mary (wants john)     to like bill |]
> bwd13 = [bwd| mary (wants everyone) to like bill |]
> bwd14 = [bwd| mary  wants           to like someone |]
> bwd15 = [bwd| mary (wants john)     to like someone |]
> bwd16 = [bwd| mary (wants everyone) to like someone |]
> bwd17 = [bwd| mary says <john     likes bill> |]
> bwd18 = [bwd| mary says <everyone likes bill> |]
> bwd19 = [bwd| mary reads a book                which  john likes |]
> bwd20 = [bwd| mary reads a book (the author of which) john likes |]
> bwd21 = [bwd| mary sees foxes   |]
> bwd22 = [bwd| mary sees the fox |]
> bwd23 = [bwd| mary sees a   fox |]


> main = $(allBwd) -- ^ collect all functions called 'bwd*' and run them


Lexicon
=======

In principle, the lexicon is made up out of Haskell functions,
wrapped up in the `Word` type, and typed with syntactic types.

There are, however, some notable differences with plain Haskell:
First off, there is the infix construct (∷) -- a stylised version
of the typing construct found in Haskell. This construct creates a
meaning postulate; a primitive function, which cannot reduce.

Secondly, there are the logical constructs: the operators (:∧),
(:⊃), (:≡) and (:≢) and the quantifiers `forall` and `exists`.

These Haskell functions can be wrapped as lexical entries, of type
`Word a`, using the function `lex_`. If you wish to write lexical
entries which are meaning postulates, you can simply define them
using the function `lex`.

Lastly, because lexical entries are directionally typed -- using
syntactic types -- they cannot be directly applied to one another.
For this reason, we provide the functions (<$) and ($>), which are
directional variations of function applications.

    Type A, B :=
        S | N | NP | INF | PP |
        A :→ B | B :← A | A :⇨ B | B :⇦ A | A :& B | Q A B C | Res A

    A  := N  :← N
    IV := NP :→ S
    TV := IV :← NP
    NS := Q NP S S

> john, mary, bill :: Word NP
> john      = lex "john"
> mary      = lex "mary"
> bill      = lex "bill"

> run, leave :: Word IV
> run       = lex "run"    ; runs   = run
> leave     = lex "leave"  ; leaves = leave

> read, see, like, serve :: Word TV
> read      = lex "read"   ; reads  = read
> see       = lex "see"    ; sees   = see
> like      = lex "like"   ; likes  = like
> serve     = lex "serve"  ; serves = serve

> say :: Word (IV :← Res S)
> say       = lex "say"    ; says   = say

> person, waiter, fox, book, author :: Word N
> person    = lex "person" ; people  = plural <$ person
> waiter    = lex "waiter" ; waiters = plural <$ waiter
> fox       = lex "fox"    ; foxes   = plural <$ fox
> book      = lex "book"   ; books   = plural <$ book
> author    = lex "author" ; authors = plural <$ author

> some, every :: Word (Q NP S S :← N)
> some      = lex_ (\f g -> exists E (\x -> f x :∧ g x))
> every     = lex_ (\f g -> forall E (\x -> f x :⊃ g x))
> a         = some
> someone   = some  <$ person
> everyone  = every <$ person

> to        = lex_ id    :: Word (INF :← IV)
> of_       = lex  "of"  :: Word ((N :→ N) :← NP)
> the       = lex  "the" :: Word (NP :← N)

> want     :: Word ((IV :← INF) :& ((IV :← INF) :← NP))
> want      = lex_ (want1 , want2)
>   where
>   wantP       = "want" ∷ T :-> E :-> T
>   want1   f x = wantP (f x) x
>   want2 y f x = wantP (f y) x
> wants     = want

> same, different :: Word (Q (Q A (NP :⇨ S) (NP :⇨ S)) S S)
> same      = lex_ same'
>   where
>   same' k = exists E (\z -> k (\k' x -> k' (\f y -> f y :∧ y :≡ z) x))
>
> different = lex_ diff1
>   where
>   diff1 k = exists (E :-> E :-> T) (\f -> diff2 f :∧ k (\k x -> k (\g y -> g y :∧ f x y) x))
>   diff2 f = forall E (\x -> forall E (\y -> not (exists E (\z -> f z x :∧ f z y))))

> type WHICH1 = Q NP NP ((N :→ N) :← (S :⇂ NP))
> type WHICH2 = Q NP NP ((N :→ N) :← (NP :⇃ S))
>
> which :: Word (WHICH1 :& WHICH2)
> which = lex_ (which',which')
>   where
>     which' f g h x = h x :∧ (g (f x))

Utility Functions
=================

> notEmpty :: (Expr E -> Expr T)  -> Expr T
> notEmpty f = exists E (\x -> f x)

> moreThanOne :: (Expr E -> Expr T)  -> Expr T
> moreThanOne f = exists E (\x -> exists E (\y -> f x :∧ f y :∧ x :≢ y))

> plural :: Word (NS :← N)
> plural = lex_ plural'
>   where
>     plural' f g =
>       exists (E :-> T) (\h -> moreThanOne h :∧ forall E (\x -> h x :⊃ (f x :∧ g x)))
