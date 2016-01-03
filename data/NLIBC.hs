{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where

import Prelude hiding (read,reads,(*),($),(<$),($>))
import NLIBC.Base


bwd0  = parseBwd S (john * runs)
{-
bwd1  = parseBwd S (john    * likes * mary)
bwd2  = parseBwd S (someone * likes * mary)
bwd3  = parseBwd S (john    * likes * everyone)
bwd4  = parseBwd S (someone * likes * everyone)
-}


-- ** LEXICON

john     = "john"   ~: NP
mary     = "mary"   ~: NP
bill     = "bill"   ~: NP

person   = "person" ~: N             --; people  = plural <$ person
waiter   = "waiter" ~: N             --; waiters = plural <$ waiter
fox      = "fox"    ~: N             --; foxes   = plural <$ fox
book     = "book"   ~: N             --; books   = plural <$ book
author   = "author" ~: N             --; authors = plural <$ author

run      = "run"    ~: IV            ; runs   = run
leave    = "leave"  ~: IV            ; leaves = leave
read     = "read"   ~: IV            ; reads  = read
see      = "see"    ~: TV            ; sees   = see
like     = "like"   ~: TV            ; likes  = like
serve    = "serve"  ~: TV            ; serves = serve
say      = "say"    ~: IV :%← SRes S ; says   = say

the      = "the"    ~: NP :%← N

some     = lam(\f -> lam(\g -> exists E (\x -> f $ x :∧ g $ x))) -: Q NP S S :%← N
every    = lam(\f -> lam(\g -> forAll E (\x -> f $ x :⊃ g $ x))) -: Q NP S S :%← N
someone  = some  <$ person
everyone = every <$ person

{-
not_empty :: EXPR ((E -> T) -> T)
not_empty f = Exists E (\x -> f $ x)

more_than_one :: EXPR ((E -> T) -> T)
more_than_one f = Exists E (\x -> Exists E (\y -> f $ x :∧ f $ y :∧ x :≢ y))

plural :: Entry (StI (NS  :← N))
plural = Entry (SStI (NS :%← N)) (EXPR tm)
  where
    tm f q =
      Exists (E :-> T) (\g -> more_than_one g :∧
        ForAll E (\x -> g $ x :⊃ (f $ x :∧ q $ g)))



-- ** Define aliases for syntactic types
-}
pattern S       = SEl SS
pattern N       = SEl SN
pattern NP      = SEl SNP
pattern PP      = SEl SPP
pattern INF     = SEl SINF
pattern Q a b c = SUnitR SHollow (c :%⇦ (a :%⇨ b))
pattern IV      = NP :%→ S
pattern TV      = IV :%← NP
pattern NS      = Q N S S

{-
-- * Example Sentences (Backward-Chaining Search)
{-
bwd0  = parseBwd S (john * runs)

bwd1  = parseBwd S (john    * likes * mary)
bwd2  = parseBwd S (someone * likes * mary)
bwd3  = parseBwd S (john    * likes * everyone)
bwd4  = parseBwd S (someone * likes * everyone)

bwd5  = parseBwd S ((the              * waiter) * serves * everyone)
bwd6  = parseBwd S ((the  * same      * waiter) * serves * everyone)
bwd7  = parseBwd S ((some * different * waiter) * serves * everyone)

bwd8  = parseBwd S (mary *  wants             * to * leave)
bwd9  = parseBwd S (mary * (wants * john)     * to * leave)
bwd10 = parseBwd S (mary * (wants * everyone) * to * leave)

bwd11 = parseBwd S (mary *  wants             * to * like * bill)
bwd12 = parseBwd S (mary * (wants * john)     * to * like * bill)
bwd13 = parseBwd S (mary * (wants * everyone) * to * like * bill)

bwd14 = parseBwd S (mary *  wants             * to * like * someone)
bwd15 = parseBwd S (mary * (wants * john)     * to * like * someone)
bwd16 = parseBwd S (mary * (wants * everyone) * to * like * someone)

bwd17 = parseBwd S (mary * says * [john     * likes * bill])
bwd18 = parseBwd S (mary * says * [everyone * likes * bill])

bwd19 = parseBwd S (mary * reads * some * book * (the * author * of' * which) * john * likes)

bwd20 = parseBwd S (mary * sees * some * fox)
bwd21 = parseBwd S (mary * sees * foxes)
bwd22 = parseBwd S (mary * sees * the  * fox)


-- * Lexicon

john      = Con "john"       -: NP
mary      = Con "mary"       -: NP
bill      = Con "bill"       -: NP
someone   = some  <$ person
everyone  = every <$ person

waiter    = Con "waiter"     -: N             ; waiters  = plural <$ waiter
fox       = Con "fox"        -: N             ; foxes    = plural <$ fox
person    = Con "person"     -: N             ; people   = plural <$ person
book      = Con "book"       -: N             ; books    = plural <$ book
author    = Con "author"     -: N             ; authors  = plural <$ author

run       = verb1 "run"      -: IV            ; runs     = run
leave     = verb1 "leave"    -: IV            ; leaves   = leave
read      = verb2 "read"     -: TV            ; reads    = read
see       = verb2 "see"      -: TV            ; sees     = see
like      = verb2 "like"     -: TV            ; likes    = like
serve     = verb2 "serve"    -: TV            ; serves   = serve
say       = verb2 "say"      -: IV :%← SRes S ; says     = say

want      = Pair want1 want2 -: (IV :%← INF) :%& ((IV :%← INF) :%← NP)
  where
  want1   = Abs (Abs (     Con "want" `App` v0 `App` (v1 `App` v0) ))
  want2   = Abs (Abs (Abs (Con "want" `App` v0 `App` (v1 `App` v2))))
wants     = want

the       = Con "the"        -: DET
some      = some1            -: Q NP S S :%← N
  where
  some1   = Abs (Abs (Exists ((App v2 v0) :∧ (App v1 v0))))
every     = every1           -: Q NP S S :%← N
  where
  every1  = Abs (Abs (Forall ((App v2 v0) :⊃ (App v1 v0))))

same      = same1            -: Q (Q A NP'S NP'S) S S
  where
  same1   = Abs (Exists (App v1 (Abs (Abs (App (App v1 (
            Abs (Abs (App v1 v0 :∧ (v0 :≡ v4))))) v0)))))
different = diff1            -: Q (Q A NP'S NP'S) S S
  where
  cond1   = Forall (Forall (Not (Exists (App (App v3 v2) v0 :∧ App (App v3 v1) v0))))
  diff1   = Abs (Exists (cond1 :∧ (App v1 (Abs (Abs (App (App v1 (
            Abs (Abs (App v1 v0 :∧ (App (App v4 v0) v2))))) v0))))))

which     = Pair whTm whTm   -: whTy1 :%& whTy2
  where
  whTm    = Abs (Abs (Abs (Abs (App v1 v0 :∧ App v2 (App v3 v0)))))
  whTy1   = Q NP NP ((N :%→ N) :%← (S :%⇂ NP))
  whTy2   = Q NP NP ((N :%→ N) :%← (NP :%→ S))

to        = Abs v0           -: INF :%← IV
of'       = Con "of"         -: (N :%→ N) :%← NP



-- * Example Sentences (Forward-Chaining Search; Experimental)

fwd0  = parseFwd S (john ∷ runs ∷ (·))

fwd1  = parseFwd S (john    ∷ likes ∷ mary ∷ (·))
fwd2  = parseFwd S (someone ∷ likes ∷ mary ∷ (·))
fwd3  = parseFwd S (john    ∷ likes ∷ everyone ∷ (·))
fwd4  = parseFwd S (someone ∷ likes ∷ everyone ∷ (·))

fwd5  = parseFwd S (the              ∷ waiter ∷ serves ∷ everyone ∷ (·))

-- don't seem to be terminating fast enough
fwd6  = parseFwd S (the  ∷ same      ∷ waiter ∷ serves ∷ everyone ∷ (·))
fwd7  = parseFwd S (some ∷ different ∷ waiter ∷ serves ∷ everyone ∷ (·))

-- cannot use `wants' because it uses additive types:
--
--fwd8  = parseFwd S (mary ∷ wants            ∷ to ∷ leave ∷ (·))
--fwd9  = parseFwd S (mary ∷ wants ∷ john     ∷ to ∷ leave ∷ (·))
--fwd10 = parseFwd S (mary ∷ wants ∷ everyone ∷ to ∷ leave ∷ (·))
--
--fwd11 = parseFwd S (mary ∷ wants            ∷ to ∷ like ∷ bill ∷ (·))
--fwd12 = parseFwd S (mary ∷ wants ∷ john     ∷ to ∷ like ∷ bill ∷ (·))
--fwd13 = parseFwd S (mary ∷ wants ∷ everyone ∷ to ∷ like ∷ bill ∷ (·))
--
--fwd14 = parseFwd S (mary ∷ wants            ∷ to ∷ like ∷ someone ∷ (·))
--fwd15 = parseFwd S (mary ∷ wants ∷ john     ∷ to ∷ like ∷ someone ∷ (·))
--fwd16 = parseFwd S (mary ∷ wants ∷ everyone ∷ to ∷ like ∷ someone ∷ (·))

fwd17 = parseFwd S (mary ∷ says ∷ john     ∷ likes ∷ bill ∷ (·))
fwd18 = parseFwd S (mary ∷ says ∷ everyone ∷ likes ∷ bill ∷ (·))

-- cannot use `which' because it uses additive types:
--
--fwd19 = parseFwd S (mary ∷ reads ∷ some ∷ book ∷ the ∷ author ∷ of' ∷ which ∷ john ∷ likes ∷ (·))

-- ???: 0 derivations
fwd20 = parseFwd S (mary ∷ sees ∷ some ∷ fox ∷ (·))

fwd21 = parseFwd S (mary ∷ sees ∷ foxes ∷ (·))


-- * Type and DSL for lexicon entries
-- * Backward-Chaining Parsing and Sentence Construction
-- * Forward-Chaining Parsing and Sentence Construction

-- TODO: this section pretty much is a testament to how I don't fully
-- understand the singletons library.

parseFwd :: SType b ->Entries xs ->  IO ()
parseFwd sb sxs = do let ps = map go (Fwd.findAll (sTypeOf sxs) sb)
                     print (length ps)
                     mapM_ putStrLn ps
  where
    go (TypedBy x Refl f) =
      case sJoinTree x sxs of (Entry _ r) -> show2 r (eta f)


infixr 4 ∷; (∷) = SCons; (·) = SNil

data Entries (xs :: [StructI]) where
  SNil  :: Entries '[]
  SCons :: Entry x -> Entries xs -> Entries (x ': xs)

sTypeOf :: Entries xs -> SList xs
sTypeOf  SNil                  = SL.SNil
sTypeOf (SCons (Entry x _) xs) = SL.SCons x (sTypeOf xs)

sJoinTree :: SStructI x -> Entries (ToList x) -> Entry x
sJoinTree (SStI a) (SCons x SNil) = x
sJoinTree (SDIA k x) env = entryDIA k (sJoinTree x env)
  where
    entryDIA :: SKind k -> Entry x -> Entry (DIA k x)
    entryDIA k (Entry x r) = Entry (SDIA k x) r
sJoinTree (SPROD k x y) env = entryPROD k (sJoinTree x xs) (sJoinTree y ys)
  where
    (xs,ys) = sBreak (fromJust (sToList x)) env
    sBreak :: SList xs -> Entries (xs :++ ys) -> (Entries xs, Entries ys)
    sBreak  SL.SNil                 env  = (SNil, env)
    sBreak (SL.SCons _ xs) (SCons x env) = first (SCons x) (sBreak xs env)
    entryPROD :: SKind k -> Entry x -> Entry y -> Entry (PROD k x y)
    entryPROD k (Entry x f) (Entry y g) = Entry (SPROD k x y) (Pair f g)


-- -}
-- -}
-- -}
-- -}
-- -}

{-
pattern S        = SEl SS
pattern N        = SEl SN
pattern NP       = SEl SNP
pattern NS       = Q NP S S
pattern PP       = SEl SPP
pattern INF      = SEl SINF
pattern A        = SEl SN :%← SEl SN
pattern IV       = SEl SNP :%→ SEl SS
pattern TV       = (SEl SNP :%→ SEl SS) :%← SEl SNP
pattern DET      = SEl SNP :%← SEl SN
pattern Q a b c  = SUnitR SHollow (c :%⇦ (a :%⇨ b))
-}
