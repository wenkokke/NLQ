{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE QuasiQuotes            #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
module Main where


import NLIBC.Base


-- ** EXAMPLES (Backward-Chaining Search)

bwd0  = [bwd| john runs |]

bwd1  = [bwd| john    likes mary     |]
bwd2  = [bwd| someone likes mary     |]
bwd3  = [bwd| john    likes everyone |]
bwd4  = [bwd| someone likes everyone |]

bwd5  = [bwd| (the           waiter) serves everyone |]
bwd6  = [bwd| (the same      waiter) serves everyone |]
bwd7  = [bwd| (a   different waiter) serves everyone |]

bwd8  = [bwd| mary  wants           to leave |]
bwd9  = [bwd| mary (wants john)     to leave |]
bwd10 = [bwd| mary (wants everyone) to leave |]

bwd11 = [bwd| mary  wants           to like bill |]
bwd12 = [bwd| mary (wants john)     to like bill |]
bwd13 = [bwd| mary (wants everyone) to like bill |]

bwd14 = [bwd| mary  wants           to like someone |]
bwd15 = [bwd| mary (wants john)     to like someone |]
bwd16 = [bwd| mary (wants everyone) to like someone |]

bwd17 = [bwd| mary says <john     likes bill> |]
bwd18 = [bwd| mary says <everyone likes bill> |]

bwd19 = [bwd| mary reads a book                which  john likes |]
bwd20 = [bwd| mary reads a book (the author of which) john likes |]

bwd21 = [bwd| mary sees foxes   |]
bwd22 = [bwd| mary sees the fox |]
bwd23 = [bwd| mary sees a   fox |]


main = $(allBwd) -- ^ collect all functions called 'bwd*' and run them


-- SYNTACTIC TYPES ------------------------ -- SEMANTIC TYPES ------------- --
--                                          --                              --
--    sentence     : S                      --    entity       : E          --
--    nouns        : N                      --    truth-value  : T          --
--    NPs          : NP                     --    functions    : a -> b     --
--    infinitives  : INF                    --    pairs        : (a , b)    --
--    PPs          : PP                     --                              --
--    over         : B :%← A                --                              --
--    under        : A :%→ B                --    or, for singletons        --
--    choice       : A :%& B                --                              --
--    quantifier   : Q A B C                --    functions    : a :-> b    --
--    scope island : SRes A                 --    pairs        : a :*  b    --
--                                          --                              --
-- ---------------------------------------- -- ---------------------------- --
--
-- SEMANTIC TERMS ------------------------- -- ENTRY CONSTRUCTION --------- --
--                                          --                              --
--    application : f $ x                   --    primitive entries:        --
--    abstraction : lam(\x -> ..)           --        name ~: type          --
--    pairs       : pair(x,y)               --                              --
--                                          --    complex entries:          --
--    universal   :  forall t (\x -> ..)    --        term -: type          --
--    existential :  exists t (\x -> ..)    --                              --
--    conjunction :  x :∧ y  or  x :/\ y    --    entry application:        --
--    implication :  x :⊃ y  or  x :=> y    --        fun <$ arg            --
--    equality    :  x :≡ y  or  x :== y    --        arg $> fun            --
--    inequality  :  x :≢ y  or  x :/= y    --                              --
--                                          --                              --
-- ---------------------------------------- -- ---------------------------- --

-- ** LEXICON

john      = "john"       ~: NP
mary      = "mary"       ~: NP
bill      = "bill"       ~: NP

person    = n "person"   -: N             ; people  = plural <$ person
waiter    = n "waiter"   -: N             ; waiters = plural <$ waiter
fox       = n "fox"      -: N             ; foxes   = plural <$ fox
book      = n "book"     -: N             ; books   = plural <$ book
author    = n "author"   -: N             ; authors = plural <$ author

run       = iv "run"     -: IV             ; runs   = run
leave     = iv "leave"   -: IV             ; leaves = leave
read      = tv "read"    -: TV             ; reads  = read
see       = tv "see"     -: TV             ; sees   = see
like      = tv "like"    -: TV             ; likes  = like
serve     = tv "serve"   -: TV             ; serves = serve
say       = tv "say"     -: IV :%← SRes S  ; says   = say
to        = lam(\f -> f) -: INF :%← IV
of'       = "of"         ~: (N :%→ N) :%← NP
the       = "the"        ~: NP :%← N

want      = pair(w1,w2)  -: (IV :%← INF) :%& ((IV :%← INF) :%← NP)
  where
    wp    = "want" ::: (E :-> T :-> T)
    w1    = lam(\f -> lam(\x -> wp $ x $ (f $ x)))
    w2    = lam(\y -> lam(\f -> lam(\x -> wp $ x $ (f $ y))))
wants     = want

a         = some
some      = lam(\f -> lam(\g -> exists E (\x -> f $ x :∧ g $ x))) -: Q NP S S :%← N
someone   = some  <$ person

every     = lam(\f -> lam(\g -> forall E (\x -> f $ x :⊃ g $ x))) -: Q NP S S :%← N
everyone  = every <$ person

same      = s1 -: Q (Q A (NP :%⇨ S) (NP :%⇨ S)) S S
  where
    s1    = lam(\k -> exists E (\z -> k $ lam(\k -> lam(\x ->
              k $ lam(\f -> lam(\y -> f $ y :∧ y :≡ z)) $ x))))

different = d1 -: Q (Q A (NP :%⇨ S) (NP :%⇨ S)) S S
  where
    c1    = lam(\f -> forall E (\x -> forall E (\y ->
              not (exists E (\z -> f $ z $ x :∧ f $ z $ y)))))
    d1    = lam(\k -> exists (E :-> E :-> T) (\f -> c1 $ f :∧ k $ lam(\k ->
              lam(\x -> k $ lam(\g -> lam(\y -> g $ y :∧ f $ x $ y)) $ x))))

which     = pair(wh,wh) -: wh1 :%& wh2
  where
    wh1   = Q NP NP ((N :%→ N) :%← (S :%⇂ NP))
    wh2   = Q NP NP ((N :%→ N) :%← (NP :%⇃ S))
    wh    = lam(\f -> lam(\g -> lam(\h -> lam(\x -> h $ x :∧ (g $ (f $ x))))))




-- ** Utility Functions

notEmpty = lam(\f -> exists E (\x -> f $ x))

moreThanOne = lam(\f -> exists E (\x -> exists E (\y -> f $ x :∧ f $ y :∧ x :≢ y)))

plural =
  lam(\f -> lam(\g ->
    exists (E :-> T) (\h -> moreThanOne $ h :∧
      forall E (\x -> h $ x :⊃ (f $ x :∧ g $ x))))) -: NS :%← N

n  n = lam(\x -> (n ::: univ) $ x)
iv n = lam(\x -> (n ::: univ) $ x)
tv n = lam(\y -> lam(\x -> (n ::: univ) $ x $ y))


-- ** Define aliases for syntactic types

pattern S       = SEl SS
pattern N       = SEl SN
pattern NP      = SEl SNP
pattern PP      = SEl SPP
pattern INF     = SEl SINF
pattern A       = N :%← N
pattern Q a b c = SUnitR SKHol (c :%⇦ (a :%⇨ b))
pattern IV      = NP :%→ S
pattern TV      = IV :%← NP
pattern NS      = Q NP S S

-- -}
-- -}
-- -}
-- -}
-- -}
