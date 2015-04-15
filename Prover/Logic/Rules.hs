module Logic.Rules where


import Prover hiding (Term)
import Logic.Base
import Logic.Parsing
import Text.Parsec (parse)


-- |Inference rules for the non-associative Lambek calculus.
nl :: [Rule ConId Int]
nl = concat [ strAxioms, strFocus, strProdAndImpLR ]

-- |Inference rules for the polarised non-associative Lambek calculus.
fnl :: [Rule ConId Int]
fnl = concat [ strPolAxioms, strPolFocus, strProdAndImpLR ]

-- |Inference rules for the classical non-associative Lambek calculus.
cnl :: [Rule ConId Int]
cnl = concat [ strAxioms, strFocus, strProdAndImpLR, strPlusAndSubLR ]

-- |Inference rules for the polarised classical non-associative Lambek calculus.
fcnl :: [Rule ConId Int]
fcnl = concat [ strPolAxioms, strPolFocus, strBoxAndDia, strZero, strOne
              , strProdAndImpLR, strPlusAndSubLR ]

-- |Inference rules for the Lambek-Grishin calculus.
lg :: [Rule ConId Int]
lg = concat [ strAxioms, strFocus, strBoxAndDia, strZero, strOne
            , strProdAndImpLR, strPlusAndSubLR, strGrishinIV ]

-- |Inference rules for the polarised Lambek-Grishin calculus.
flg :: [Rule ConId Int]
flg = concat [ strPolAxioms, strPolFocus, strBoxAndDia, strZero, strOne
             , strProdAndImpLR, strPlusAndSubLR, strGrishinIV ]

-- |Inference rules for an experimental version of the Lambek calculus.
exp :: [Rule ConId Int]
exp = concat [ strPolAxioms, strPolFocus, strProdAndImpLR, strIsland ]

-- |Inference rules for the non-associative Lambek calculus.
algnl :: [Rule ConId Int]
algnl = concat [ algAxiom, algProdAndImpLR ]

-- |Inference rules for the non-associative Lambek calculus.
algnlcl :: [Rule ConId Int]
algnlcl = concat [ algAxiom, algProdAndImpLR, algHollowProdAndImpLR, algConst]


-- |Inference rules for axioms.
strAxioms :: [Rule ConId Int]
strAxioms =
  [ (([] ⟶ "[ A ] ⊢ . A .") "ax⁻") { guard = atomA }
  , (([] ⟶ ". B . ⊢ [ B ]") "ax⁺") { guard = atomB }
  ]
  where
    atomA (Con JFocusL [Con (Atom _) [], _]) = True; atomA _ = False
    atomB (Con JFocusR [_, Con (Atom _) []]) = True; atomB _ = False

-- |Structural, polarised inference rules for axioms.
strPolAxioms :: [Rule ConId Int]
strPolAxioms =
  [ (([] ⟶ "[ A ] ⊢ . A .") "ax⁻") { guard = atomA }
  , (([] ⟶ ". B . ⊢ [ B ]") "ax⁺") { guard = atomB }
  ]
  where
    atomA (Con JFocusL [Con (Atom a) [], _]) = isNegativeAtom a; atomA _ = False
    atomB (Con JFocusR [_, Con (Atom b) []]) = isPositiveAtom b; atomB _ = False



-- |Structural inference rules for focusing and unfocusing.
strFocus :: [Rule ConId Int]
strFocus =
  [ (["  X   ⊢ . B ."] ⟶ "  X   ⊢ [ B ]") "⇁"
  , ([". A . ⊢   Y  "] ⟶ "[ A ] ⊢   Y  ") "↽"
  , (["  X   ⊢ [ B ]"] ⟶ "  X   ⊢ . B .") "⇀"
  , (["[ A ] ⊢   Y  "] ⟶ ". A . ⊢   Y  ") "↼"
  ]

-- |Structural, polarised inference rules for focusing and unfocusing.
strPolFocus :: [Rule ConId Int]
strPolFocus =
  [ ((["  X   ⊢ . B ."] ⟶ "  X   ⊢ [ B ]") "⇁") { guard = negB }
  , (([". A . ⊢   Y  "] ⟶ "[ A ] ⊢   Y  ") "↽") { guard = posA }
  , ((["  X   ⊢ [ B ]"] ⟶ "  X   ⊢ . B .") "⇀") { guard = posB }
  , ((["[ A ] ⊢   Y  "] ⟶ ". A . ⊢   Y  ") "↼") { guard = negA }
  ]
  where
    posA (Con JFocusL [a, _])            = pos a; posA _ = False
    negB (Con JFocusR [_, b])            = neg b; negB _ = False
    negA (Con JStruct [Con Down [a], _]) = neg a; negA _ = False
    posB (Con JStruct [_, Con Down [b]]) = pos b; posB _ = False

-- |Structural left- and right rules for island constraints.
strIsland :: [Rule ConId Int]
strIsland =
  [ (["⟨ . A . ⟩ ⊢     Y    "] ⟶ ". ◇ A . ⊢     Y  ") "◇ᴸ"
  , (["    X     ⊢ [   B   ]"] ⟶ "⟨   X ⟩ ⊢ [ ◇ B ]") "◇ᴿ"
  ]

-- |Structural residuation and left- and right rules for (◇, □).
strBoxAndDia :: [Rule ConId Int]
strBoxAndDia =
  [ (["⟨ . A . ⟩ ⊢     Y    "] ⟶ ". ◇ A . ⊢     Y  ") "◇ᴸ"
  , (["    X     ⊢ [   B   ]"] ⟶ "⟨   X ⟩ ⊢ [ ◇ B ]") "◇ᴿ"
  , (["[   A   ] ⊢     Y    "] ⟶ "[ □ A ] ⊢ [   Y ]") "□ᴸ"
  , (["    X     ⊢ [ . A . ]"] ⟶ "    X   ⊢ . □ A .") "□ᴿ"
  , (["    X     ⊢ [   Y   ]"] ⟶ "⟨   X ⟩ ⊢     Y  ") "r□◇"
  , (["⟨   X   ⟩ ⊢     Y    "] ⟶ "    X   ⊢ [   Y ]") "r◇□"
  ]

-- |Structural residuation and left- and right rules for  (₀ , ⁰).
strZero :: [Rule ConId Int]
strZero =
  [ (["X ⊢   [ A ]  "] ⟶ "[ ₀ A ]   ⊢   ₀ X    ") "₀ᴸ "
  , (["X ⊢ ₀ · A ·  "] ⟶ "    X     ⊢ · ₀ A   ·") "₀ᴿ "
  , (["X ⊢   [ A ]  "] ⟶ "[   A ⁰ ] ⊢     X ⁰  ") "⁰ᴸ "
  , (["X ⊢   · A · ⁰"] ⟶ "    X     ⊢ ·   A ⁰ ·") "⁰ᴿ "
  , (["X ⊢     Y   ⁰"] ⟶ "    Y     ⊢   ₀ X    ") "r⁰₀"
  , (["Y ⊢ ₀   X    "] ⟶ "    X     ⊢     Y ⁰  ") "r₀⁰"
  ]

-- |Structural residuation and left- and right rules for (₁ , ¹).
strOne :: [Rule ConId Int]
strOne =
  [ (["₁ · A ·   ⊢ Y"] ⟶ "· ₁ A   · ⊢    Y    ") "₁ᴸ "
  , (["  [ A ]   ⊢ Y"] ⟶ "  ₁ Y     ⊢[ ₁ A ]  ") "₁ᴿ "
  , (["  · A · ¹ ⊢ Y"] ⟶ "·   A ¹ · ⊢    Y    ") "¹ᴸ "
  , (["  [ A ]   ⊢ Y"] ⟶ "    Y ¹   ⊢[   A ¹ ]") "¹ᴿ "
  , (["    X   ¹ ⊢ Y"] ⟶ "  ₁ Y     ⊢    X    ") "r¹₁"
  , (["₁   Y     ⊢ X"] ⟶ "    X ¹   ⊢    Y    ") "r₁¹"
  ]

-- |Structural residuation and left- and right rules for (⇐, ⊗, ⇒).
strProdAndImpLR :: [Rule ConId Int]
strProdAndImpLR =
  [ (["· A · ⊗ · B · ⊢ Y"]    ⟶ "· A ⊗ B · ⊢ Y"    ) "⊗ᴸ"
  , (["X ⊢[ A ]","Y ⊢[ B ]"]  ⟶ "X ⊗ Y ⊢[ A ⊗ B ]" ) "⊗ᴿ"
  , (["X ⊢[ A ]", "[ B ]⊢ Y"] ⟶ "[ A ⇒ B ]⊢ X ⇒ Y" ) "⇒ᴸ"
  , (["X ⊢ · A · ⇒ · B ·"]    ⟶ "X ⊢ · A ⇒ B ·"    ) "⇒ᴿ"
  , (["X ⊢[ A ]", "[ B ]⊢ Y"] ⟶ "[ B ⇐ A ]⊢ Y ⇐ X" ) "⇐ᴸ"
  , (["X ⊢ · B · ⇐ · A ·"]    ⟶ "X ⊢ · B ⇐ A ·"    ) "⇐ᴿ"
  , (["Y ⊢ X ⇒ Z"]            ⟶ "X ⊗ Y ⊢ Z "       ) "r⇒⊗"
  , (["X ⊗ Y ⊢ Z"]            ⟶ "Y ⊢ X ⇒ Z "       ) "r⊗⇒"
  , (["X ⊢ Z ⇐ Y"]            ⟶ "X ⊗ Y ⊢ Z "       ) "r⇐⊗"
  , (["X ⊗ Y ⊢ Z"]            ⟶ "X ⊢ Z ⇐ Y "       ) "r⊗⇐"
  ]

-- |Structural residuation and left- and right rules for (⇚, ⊕, ⇛).
strPlusAndSubLR :: [Rule ConId Int]
strPlusAndSubLR =
  [ (["[ B ]⊢ Y", "[ A ]⊢ X"] ⟶ "[ B ⊕ A ]⊢ Y ⊕ X" ) "⊕ᴸ"
  , (["X ⊢ · B · ⊕ · A ·"]    ⟶ "X ⊢ · B ⊕ A ·"    ) "⊕ᴿ"
  , (["· A · ⇚ · B · ⊢ X"]    ⟶ "· A ⇚ B · ⊢ X"    ) "⇚ᴸ"
  , (["X ⊢[ A ]", "[ B ]⊢ Y"] ⟶ "X ⇚ Y ⊢[ A ⇚ B ]" ) "⇚ᴿ"
  , (["· B · ⇛ · A · ⊢ X"]    ⟶ "· B ⇛ A · ⊢ X"    ) "⇛ᴸ"
  , (["X ⊢[ A ]", "[ B ]⊢ Y"] ⟶ "Y ⇛ X ⊢[ B ⇛ A ]" ) "⇛ᴿ"
  , (["Z ⇚ X ⊢ Y"]            ⟶ "Z ⊢ Y ⊕ X"        ) "r⇚⊕"
  , (["Z ⊢ Y ⊕ X"]            ⟶ "Z ⇚ X ⊢ Y"        ) "r⊕⇚"
  , (["Y ⇛ Z ⊢ X"]            ⟶ "Z ⊢ Y ⊕ X"        ) "r⇛⊕"
  , (["Z ⊢ Y ⊕ X"]            ⟶ "Y ⇛ Z ⊢ X"        ) "r⊕⇛"
  ]

-- |Structural Grishin interaction postulates IV.
strGrishinIV :: [Rule ConId Int]
strGrishinIV =
  [ (["X ⊗ Y ⊢ Z ⊕ W"]        ⟶ "Z ⇛ X ⊢ W ⇐ Y"    ) "d⇛⇐"
  , (["X ⊗ Y ⊢ Z ⊕ W"]        ⟶ "Z ⇛ Y ⊢ X ⇒ W"    ) "d⇛⇒"
  , (["X ⊗ Y ⊢ Z ⊕ W"]        ⟶ "Y ⇚ W ⊢ X ⇒ Z"    ) "d⇚⇒"
  , (["X ⊗ Y ⊢ Z ⊕ W"]        ⟶ "X ⇚ W ⊢ Z ⇐ Y"    ) "d⇚⇐"
  ]


-- |Algebraic axiom.
algAxiom :: [Rule ConId Int]
algAxiom =
  [ ([] ⟶ "A ⊢ A") "ax′" ]


-- |Algebraic residuation and monotonicity rules for (⇐, ⊗, ⇒).
algProdAndImpLR :: [Rule ConId Int]
algProdAndImpLR =
  [ (["A ⊢ B", "C ⊢ D"] ⟶ "A ⊗ C ⊢ B ⊗ D") "m⊗"
  , (["A ⊢ B", "C ⊢ D"] ⟶ "B ⇒ C ⊢ A ⇒ D") "m⇒"
  , (["A ⊢ B", "C ⊢ D"] ⟶ "A ⇐ D ⊢ B ⇐ C") "m⇐"
  , (["B ⊢ A ⇒ C"]      ⟶ "A ⊗ B ⊢ C"    ) "r⇒⊗"
  , (["A ⊗ B ⊢ C"]      ⟶ "B ⊢ A ⇒ C"    ) "r⊗⇒"
  , (["A ⊢ C ⇐ B"]      ⟶ "A ⊗ B ⊢ C"    ) "r⇐⊗"
  , (["A ⊗ B ⊢ C"]      ⟶ "A ⊢ C ⇐ B"    ) "r⊗⇐"
  ]

-- |Algebraic residuation and monotonicity rules for (⇦, ∘, ⇨).
algHollowProdAndImpLR :: [Rule ConId Int]
algHollowProdAndImpLR =
  [ (["A ⊢ B", "C ⊢ D"] ⟶ "A ∘ C ⊢ B ∘ D") "m∘"
  , (["A ⊢ B", "C ⊢ D"] ⟶ "B ⇨ C ⊢ A ⇨ D") "m⇨"
  , (["A ⊢ B", "C ⊢ D"] ⟶ "A ⇦ D ⊢ B ⇦ C") "m⇦"
  , (["B ⊢ A ⇨ C"]      ⟶ "A ∘ B ⊢ C"    ) "r⇨∘"
  , (["A ∘ B ⊢ C"]      ⟶ "B ⊢ A ⇨ C"    ) "r∘⇨"
  , (["A ⊢ C ⇦ B"]      ⟶ "A ∘ B ⊢ C"    ) "r⇦∘"
  , (["A ∘ B ⊢ C"]      ⟶ "A ⊢ C ⇦ B"    ) "r∘⇦"
  ]

-- |Algebraic rules for (I, L, R) referred to as (I, B, C) in
--  Barker & Shan (2014).
algConst :: [Rule ConId Int]
algConst =
  [ (["A ⊢ B"]                 ⟶ "A ∘ I ⊢ B"            ) "Iᵢ"
  , (["A ∘ I ⊢ B"]             ⟶ "A ⊢ B"                ) "Iₑ"
  , (["A ⊗ (B ∘ C) ⊢ D"]       ⟶ "B ∘ ((L ⊗ A) ⊗ C) ⊢ D") "Lᵢ"
  , (["B ∘ ((L ⊗ A) ⊗ C) ⊢ D"] ⟶ "A ⊗ (B ∘ C) ⊢ D"      ) "Lₑ"
  , (["(A ∘ B) ⊗ C ⊢ D"]       ⟶ "A ∘ ((R ⊗ B) ⊗ C) ⊢ D") "Rᵢ"
  , (["A ∘ ((R ⊗ B) ⊗ C) ⊢ D"] ⟶ "(A ∘ B) ⊗ C ⊢ D"      ) "Rₑ"
  ]


infixr 1 ⟶

(⟶) :: [String] -> String -> RuleId -> Rule ConId Int
(⟶) ps c n =
    case mapM (parse judgementVar "Rules.hs") ps of
     Left err  -> error ("Cannot parse premises of rule `"++n++"' in `Rules.hs'.\n"++show err)
     Right ps' ->
       case parse judgementVar "Rules.hs" c of
        Left err -> error ("Cannot parse conclusion of rule `"++n++"' in `Rules.hs'.\n"++show err)
        Right c' -> mkRule ps' c' n
