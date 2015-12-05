{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where


import           Prelude         hiding (pred,read,reads,(<$),(*))
import           Data.List       (nub)
import           Data.Singletons.Prelude
import           Data.Singletons (fromSing)
import           NLIBC.Syntax.Backward
import qualified NLIBC.Syntax.Backward as Syn
import           NLIBC.Syntax.Base hiding (Q,T,S,N,NP,PP,INF)
import qualified NLIBC.Syntax.Base as Syn (Q,T,Atom(..))
import           NLIBC.Semantics (HI,HO,H,E,T,v0,v1,v2,v3,v4,eta)
import qualified NLIBC.Semantics as Sem
import           NLIBC.Semantics.Show2
import           Text.Printf (printf)


infixr 3 *; (*) = (,)
infixr 4 ∷; (∷) = SCons




-- * Example Sentences (Backward-Chaining Search)

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



-- * Utility Functions

-- |Create an entry for an intransitive verb.
verb1 iv = Con iv

-- |Create an entry for a transitive verb.
verb2 tv = Abs (Abs (App (App (Con tv) v0) v1))

-- |Expression enforcing that a predicate is non-empty.
not_empty :: Repr ts ((E -> T) -> T)
not_empty = Abs (Exists (App v1 v0))

-- |Expression enforcing that a predicate has at least two members.
more_than_one :: Repr ts ((E -> T) -> T)
more_than_one = Abs (Exists (Exists ((App v2 v1 :∧ App v2 v0) :∧ (v1 :≢ v0))))

-- |Left application for entries.
(<$) :: Entry (StI (b :← a)) -> Entry (StI a) -> Entry (StI b)
(Entry (SStI (b :%← _)) f) <$ (Entry (SStI _) x) = Entry (SStI b) (App f x)

-- |Right application for entries.
($>) :: Entry (StI a) -> Entry (StI (a :→ b)) -> Entry (StI b)
(Entry (SStI _) x) $> (Entry (SStI (_ :%→ b)) f) = Entry (SStI b) (App f x)

-- |Expression transforming nouns into plural nouns.
plural :: Entry (StI (NS :← N))
plural = Entry (SStI (NS :%← N))
  (Abs (Abs (Exists (App more_than_one v0
    :∧ Forall (App v1 v0 :⊃ (App v3 v0 :∧ App v2 v0))))))


type    S        = El 'Syn.S
type    N        = El 'Syn.N
type    NP       = El 'Syn.NP
type    PP       = El 'Syn.PP
type    INF      = El 'Syn.INF
type    NP'S     = NP :⇨ S
type    NS       = Q NP S S
type    A        = N :← N
type    IV       = NP :→ S
type    TV       = (NP :→ S) :← NP
type    DET      = NP :← N
type    Q a b c  = UnitR Hollow (c :⇦ (a :⇨ b))


pattern S        = SEl SS
pattern N        = SEl SN
pattern NP       = SEl SNP
pattern NP'S     = NP :%⇨ S
pattern NS       = Q NP S S
pattern PP       = SEl SPP
pattern INF      = SEl SINF
pattern A        = SEl SN :%← SEl SN
pattern IV       = SEl SNP :%→ SEl SS
pattern TV       = (SEl SNP :%→ SEl SS) :%← SEl SNP
pattern DET      = SEl SNP :%← SEl SN
pattern Q a b c  = SUnitR SHollow (c :%⇦ (a :%⇨ b))

pattern Forall u = App (Con "∀") (Abs u)
pattern Exists u = App (Con "∃") (Abs u)
pattern Not  x   = App (Con "¬") x
pattern x :∧ y   = App (App (Con "∧") x) y
pattern x :⊃ y   = App (App (Con "⊃") x) y
pattern x :≡ y   = App (App (Con "≡") x) y
pattern x :≢ y   = Not (x :≡ y)



-- * DSL for lexicons and parses

data Entry x = Entry (SStructI x) (Repr '[] (HI x))


instance Show (Entry x) where
  show (Entry t r) = show r

infix 1 -:

(-:) :: Repr '[] (H a) -> SType a -> Entry (StI a)
r -: t = Entry (SStI t) r

class Combine a b | a -> b where
  combine :: a -> b

instance Combine (Entry t) (Entry t) where
  combine = id

instance (Combine x (Entry a))
         => Combine [x] (Entry (DIA Reset a)) where
  combine [x] = case combine x of
    (Entry a r) -> Entry (SDIA SReset a) r

instance (Combine x1 (Entry a1), Combine x2 (Entry a2))
         => Combine (x1,x2) (Entry (a1 :∙ a2))
  where
    combine (x1,x2) = case (combine x1,combine x2) of
      (Entry a1 r1,Entry a2 r2) -> Entry (a1 :%∙ a2) (Pair r1 r2)


parseBwd :: Combine x (Entry a) => SType b -> x -> IO ()
parseBwd b e = case combine e of
  Entry x r -> do let ps = show2 r . eta <$> findAll (x :%⊢ SStO b)
                  print (length ps)
                  mapM_ putStrLn ps






-- This file contains example sentences treated with my extension of
-- NLIBC, which is capable of expressing quantifiers, scope islands,
-- infixation and extraction.
--
-- The `findAll` statements will search for proofs in the grammar
-- logic for the given sequent, which can then be interpreted
-- semantically using the `eta` function.
--
-- For purposes of presentation, the `show2` function is applied,
-- which -- when given some lambda term representations for the words
-- in the sentence -- will compute the sentence representation. This
-- means that the sentence meaning is converted to normal-form, the
-- word meanings are inserted in the appropriate places, and
-- quantifiers and such are resolved. Keep in mind, though, that this
-- step is only there to get a string representation of the term, and
-- that the sentence meaning can be anything that forms a simply-typed
-- lambda calculus with products and units.
--
-- Note: the notation used for lambda terms is based on the one used
-- in formal semantics. The most confusing feature is the fact that
-- the application of a postulate -- e.g. person -- is written in the
-- traditional mathematical style -- i.e. person(x) -- whereas the
-- application of a composite function is written in functional
-- style. Additionally, the calculus has some syntactic sugar for the
-- quantifiers -- ∀x.u abbreviates ∀(λx.u) and likewise for ∃ -- and
-- is extended with postulates for the logical connectives.

-- -}
-- -}
-- -}
-- -}
-- -}
