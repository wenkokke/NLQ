------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                   using (id; const; _$_; _∘_)
open import Data.Bool                  using (Bool; true; false; if_then_else_; not)
open import Data.Char                  using (Char)
open import Data.List                  using (List; _∷_; []; concatMap; map; filter; null)
open import Data.String                using (String; unlines; fromList; _++_) renaming (_≟_ to _≟-String_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Reflection                 hiding (name; constructor′)


module Export.LaTeX.SyntaxDecl where


open import Export.LaTeX.Base (const false)
module S = Show ""


argNames : Type → List String
argNames (el _ (pi (arg _                    _) (abs "_" t))) =     argNames t
argNames (el s (pi (arg (arg-info visible _) _) (abs  x  t))) = x ∷ argNames t
argNames (el s (pi (arg (arg-info _       _) _) (abs  x  t))) =     argNames t
argNames _                                                    = []


_namesOf_ : Type → Name → List String
(el _ (pi (arg i _               ) (abs "_" t₂))) namesOf n′ = t₂ namesOf n′
(el _ (pi (arg i (el _ (def n _))) (abs  x  t₂))) namesOf n′ =
  if ⌊ unqualifiedName n ≟-String unqualifiedName n′ ⌋ then x ∷ (t₂ namesOf n′) else (t₂ namesOf n′)
_ namesOf _  = []


showCon : Name → String
showCon n = S.oper S.agdaCon (unqualifiedName n) (map S.agdaVar (argNames (type n)))


nub : List String → List String
nub [] = []
nub (x ∷ xs) = x ∷ filter (λ y → not ⌊ x ≟-String y ⌋) (nub xs)


asSyntaxDecl′ : (datatype : Name) (partial? : Bool) (variables : List String) (constructors : List Name) → String
asSyntaxDecl′ datatype partial?  variables constructors
  = unlines
  $ "\\begin{spec}"
  ∷ "\\>[0]\\AgdaIndent{2}{}\\<[2]%"
  ∷ ("\\>[2]" ++ dt-name ++ joinWith " \\AgdaSymbol{,} " dt-vars
     ++ " \\AgdaSymbol{:=} " ++ joinWith " \\AgdaSymbol{|} " (dt-dots dt-pats)
     ++ "\\<%"
    )
  ∷ "\\end{spec}"
  ∷ []
  where
    dt-dots = if partial? then ("\\AgdaSymbol{\\ldots}" ∷_) else id
    dt-name = S.agdaDef (unqualifiedName datatype)
    dt-pats = map showCon constructors
    dt-vars = if null variables
                 then map S.agdaVar ∘ nub $
                      concatMap (λ n′ → (type n′) namesOf datatype) constructors
                 else variables



asSyntaxDecl : Name → String
asSyntaxDecl name with definition name
asSyntaxDecl name | data-type datatype = asSyntaxDecl′ name false [] (constructors datatype)
asSyntaxDecl name | _                  = "error: " ++ unqualifiedName name ++ " is not a data-type."


asSyntaxDeclOf : Name → List Name → String
asSyntaxDeclOf name constructors = asSyntaxDecl′ name true [] constructors


asConstructorOf : Name → Name → String
asConstructorOf name constructor′ = asSyntaxDeclOf name (constructor′ ∷ [])
