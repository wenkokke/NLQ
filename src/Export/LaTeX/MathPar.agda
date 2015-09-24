------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Export Agda data types to LaTeX inference rules.
--
--  * Requires `mathpartir.sty` to be available.
--
--  * The module has a parameter called `bannedArg`, which can be used
--    to hide certain names. This is useful to hide module parameters,
--    which present as visible arguments in the syntax tree and
--    therefore mess up the printing of mixfix operators.
--
--  * Exposes `_asMathParOf_`, which takes a list of names and the
--    name of a data type, and typesets those names as inference rules
--    of the data type. Furthermore it will add the name of the data
--    type to the list of banned arguments. The reasoning behind this
--    is that you would set up your data type as below and would not
--    want the `Λ` to be printed:
--
--      data Sequent : Set where _⊢_ : List Type → Type → Sequent
--      data Λ_ : Sequent → Set where ...
--
--    If you do not want this behaviour, you can use `asMathPar`.
--
--  * Exposes `asMathPar`, which takes a name and typesets it as an
--    inference rules. In the case where the name is a data-type, it
--    will fetch the constructors of that data-type and feed them into
--    `_asMathParOf_`, as described above.
--
--  * Exposes `_asInferRuleOf_` as a shortcut for `_asMathParOf_` with
--    a single rule.
--
--  * The layout of the inference rules is chosen as follows:
--
--    - If the successive inference rules start with the same
--      character, the system will try to keep them on the same line.
--    - Otherwise, the system will insert a line break.
--    - If this procedure would insert a line break after every
--      inference rule, the system will choose to keep them on the
--      same line instead .
--
------------------------------------------------------------------------


open import Category.Monad     using (module RawMonad)
open import Data.Bool          using (Bool; true; false; not; if_then_else_; _∧_)
open import Data.Char          using (Char; _==_)
open import Data.List          using (List; _∷_; []; [_])
open import Data.String        using (String; toList; fromList)
open import Reflection         using (Name; definition; data-type; constructors)


module Export.LaTeX.MathPar (bannedArg : Name → Bool) where


open RawMonad {{...}} using (_<$>_)
open import Export.LaTeX.Base bannedArg

private
  -- Layout lists of rules according to the following idea: We put line breaks
  -- between two rules if their first characters are not the same, unless this
  -- would create a sequence of rules which all are put on their own line.
  layout : (Name → String) → List Name → String
  layout f []       = ""
  layout f (n ∷ []) = f n
  layout f (n ∷ ns) =
    joinWith "\\\\\\\\" (joinWith "\\and" <$> ((f <$>_) <$> merge (groupBy _H==_ n ns)))
    where
    _H==_ : Name → Name → Bool
    _H==_ x y with toList (unqualifiedName x) | toList (unqualifiedName y)
    _H==_ _ _ |     [] |     [] = true
    _H==_ _ _ | x ∷ xs | y ∷ ys = x == y
    _H==_ _ _ | _      | _      = false

    _∷₁_ : ∀ {a} {A : Set a} → A → List (List A) → List (List A)
    x ∷₁ [] = [ [ x ] ]
    x ∷₁ (xs ∷ xss) = (x ∷ xs) ∷ xss

    groupBy : ∀ {a} {A : Set a} (eq : A → A → Bool) → A → List A → List (List A)
    groupBy eq x []       = [ [ x ] ]
    groupBy eq x (y ∷ []) = if eq x y then [ x ∷ y ∷ [] ] else [ x ] ∷ [ y ] ∷ []
    groupBy eq x (y ∷ ys) = if eq x y then x ∷₁ (groupBy eq y ys) else [ x ] ∷ groupBy eq y ys

    merge : ∀ {a} {A : Set a} → List (List A) → List (List A)
    merge []                          = []
    merge ((x ∷ []) ∷ (y ∷ []) ∷ xss) = x ∷₁ merge ((y ∷ []) ∷ xss)
    merge (xs ∷ xss)                  = xs ∷ merge xss



asMathParOf : Name → List Name → String
asMathParOf datatype constructors
  = mathpar (layout (Show.asInferRule (asString datatype)) constructors)


asInferRuleOf : Name → Name → String
asInferRuleOf datatype constructor′
  = asMathParOf datatype (constructor′ ∷ [])


asMathPar : Name → String
asMathPar name with definition name
asMathPar name | data-type datatype = asMathParOf name (constructors datatype)
asMathPar name | _                  = mathpar (Show.asInferRule "" name)
