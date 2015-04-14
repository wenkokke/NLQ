module Logic.Rules where


import Prover hiding (Term)
import Logic.Base
import Logic.Parsing


-- |Inference rules for the non-associative Lambek calculus.
nl :: [Rule ConId Int]
nl = concat [axioms, focusing, prodAndImpLR]

-- |Inference rules for the non-associative Lambek calculus.
nlcl :: [Rule ConId Int]
nlcl = concat [axioms, focusing, prodAndImpLR1, prodAndImpLR2, constILR]

-- |Inference rules for the polarised non-associative Lambek calculus.
fnl :: [Rule ConId Int]
fnl = concat [polarisedAxioms, polarisedFocusing, prodAndImpLR]


-- |Inference rules for the classical non-associative Lambek calculus.
cnl :: [Rule ConId Int]
cnl = concat [axioms, focusing, prodAndImpLR, plusAndSubLR]


-- |Inference rules for the polarised classical non-associative Lambek calculus.
fcnl :: [Rule ConId Int]
fcnl = concat [ polarisedAxioms, polarisedFocusing, boxAndDia, zero, one
              , prodAndImpLR, plusAndSubLR
              ]


-- |Inference rules for the Lambek-Grishin calculus.
lg :: [Rule ConId Int]
lg = concat [ axioms, focusing, boxAndDia, zero, one, prodAndImpLR, plusAndSubLR
            , grishinIV
            ]


-- |Inference rules for the polarised Lambek-Grishin calculus.
flg :: [Rule ConId Int]
flg = concat [ polarisedAxioms, polarisedFocusing, boxAndDia, zero, one
             , prodAndImpLR, plusAndSubLR, grishinIV
             ]

-- |Inference rules for an experimental version of the Lambek calculus.
exp :: [Rule ConId Int]
exp = concat [ polarisedAxioms, polarisedFocusing, prodAndImpLR, island ]


-- |Inference rules for axioms.
axioms :: [Rule ConId Int]
axioms =
  [ (([] ⟶ "[ A ] ⊢ . A .") "ax⁻") { guard = atomA }
  , (([] ⟶ ". B . ⊢ [ B ]") "ax⁺") { guard = atomB }
  ]
  where
    atomA (Con JFocusL [Con (Atom _) [], _]) = True; atomA _ = False
    atomB (Con JFocusR [_, Con (Atom _) []]) = True; atomB _ = False

-- |Polarised inference rules for axioms.
polarisedAxioms :: [Rule ConId Int]
polarisedAxioms =
  [ (([] ⟶ "[ A ] ⊢ . A .") "ax⁻") { guard = atomA }
  , (([] ⟶ ". B . ⊢ [ B ]") "ax⁺") { guard = atomB }
  ]
  where
    atomA (Con JFocusL [Con (Atom a) [], _]) = isNegativeAtom a; atomA _ = False
    atomB (Con JFocusR [_, Con (Atom b) []]) = isPositiveAtom b; atomB _ = False



-- |Inference rules for focusing and unfocusing.
focusing :: [Rule ConId Int]
focusing =
  [ (["  X   ⊢ . B ."] ⟶ "  X   ⊢ [ B ]") "⇁"
  , ([". A . ⊢   Y  "] ⟶ "[ A ] ⊢   Y  ") "↽"
  , (["  X   ⊢ [ B ]"] ⟶ "  X   ⊢ . B .") "⇀"
  , (["[ A ] ⊢   Y  "] ⟶ ". A . ⊢   Y  ") "↼"
  ]

-- |Polarised inference rules for focusing and unfocusing.
polarisedFocusing :: [Rule ConId Int]
polarisedFocusing =
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

-- |Rules for island constraints.
island :: [Rule ConId Int]
island =
  [ (["⟨ . A . ⟩ ⊢     Y    "] ⟶ ". ◇ A . ⊢     Y  ") "◇ᴸ"
  , (["    X     ⊢ [   B   ]"] ⟶ "⟨   X ⟩ ⊢ [ ◇ B ]") "◇ᴿ"
  ]

-- |Residuation and monotonicity rules for (□ , ◇)
boxAndDia :: [Rule ConId Int]
boxAndDia =
  [ (["⟨ . A . ⟩ ⊢     Y    "] ⟶ ". ◇ A . ⊢     Y  ") "◇ᴸ"
  , (["    X     ⊢ [   B   ]"] ⟶ "⟨   X ⟩ ⊢ [ ◇ B ]") "◇ᴿ"
  , (["[   A   ] ⊢     Y    "] ⟶ "[ □ A ] ⊢ [   Y ]") "□ᴸ"
  , (["    X     ⊢ [ . A . ]"] ⟶ "    X   ⊢ . □ A .") "□ᴿ"
  , (["    X     ⊢ [   Y   ]"] ⟶ "⟨   X ⟩ ⊢     Y  ") "r□◇"
  , (["⟨   X   ⟩ ⊢     Y    "] ⟶ "    X   ⊢ [   Y ]") "r◇□"
  ]

-- |Residuation and monotonicity rules for (₀ , ⁰)
zero :: [Rule ConId Int]
zero =
  [ (["X ⊢   [ A ]  "] ⟶ "[ ₀ A ]   ⊢   ₀ X    ") "₀ᴸ "
  , (["X ⊢ ₀ · A ·  "] ⟶ "    X     ⊢ · ₀ A   ·") "₀ᴿ "
  , (["X ⊢   [ A ]  "] ⟶ "[   A ⁰ ] ⊢     X ⁰  ") "⁰ᴸ "
  , (["X ⊢   · A · ⁰"] ⟶ "    X     ⊢ ·   A ⁰ ·") "⁰ᴿ "
  , (["X ⊢     Y   ⁰"] ⟶ "    Y     ⊢   ₀ X    ") "r⁰₀"
  , (["Y ⊢ ₀   X    "] ⟶ "    X     ⊢     Y ⁰  ") "r₀⁰"
  ]

-- |Residuation and monotonicity rules for (₀ , ⁰ , ₁ , ¹)
one :: [Rule ConId Int]
one =
  [ (["₁ · A ·   ⊢ Y"] ⟶ "· ₁ A   · ⊢    Y    ") "₁ᴸ "
  , (["  [ A ]   ⊢ Y"] ⟶ "  ₁ Y     ⊢[ ₁ A ]  ") "₁ᴿ "
  , (["  · A · ¹ ⊢ Y"] ⟶ "·   A ¹ · ⊢    Y    ") "¹ᴸ "
  , (["  [ A ]   ⊢ Y"] ⟶ "    Y ¹   ⊢[   A ¹ ]") "¹ᴿ "
  , (["    X   ¹ ⊢ Y"] ⟶ "  ₁ Y     ⊢    X    ") "r¹₁"
  , (["₁   Y     ⊢ X"] ⟶ "    X ¹   ⊢    Y    ") "r₁¹"
  ]

-- |Residuation and monotonicity rules for (⇐, ⊗, ⇒)
prodAndImpLR :: [Rule ConId Int]
prodAndImpLR =
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

-- |Residuation and monotonicity rules for (⇚, ⊕, ⇛)
plusAndSubLR :: [Rule ConId Int]
plusAndSubLR =
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

-- |Grishin interaction postulates IV.
grishinIV :: [Rule ConId Int]
grishinIV =
  [ (["X ⊗ Y ⊢ Z ⊕ W"]        ⟶ "Z ⇛ X ⊢ W ⇐ Y"    ) "d⇛⇐"
  , (["X ⊗ Y ⊢ Z ⊕ W"]        ⟶ "Z ⇛ Y ⊢ X ⇒ W"    ) "d⇛⇒"
  , (["X ⊗ Y ⊢ Z ⊕ W"]        ⟶ "Y ⇚ W ⊢ X ⇒ Z"    ) "d⇚⇒"
  , (["X ⊗ Y ⊢ Z ⊕ W"]        ⟶ "X ⇚ W ⊢ Z ⇐ Y"    ) "d⇚⇐"
  ]



-- * Barker & Shan rules for NLCL.


-- |Residuation and monotonicity rules for (⇐, ⊗, ⇒) as second pair of (⇐, ⊗, ⇒)
prodAndImpLR1 :: [Rule ConId Int]
prodAndImpLR1 =
  [ (["A ⊢ B", "C ⊢ D"] ⟶ "A ∙ C ⊢ B ∙ D") "m∙"
  , (["A ⊢ B", "C ⊢ D"] ⟶ "B ⇒ C ⊢ A ⇒ D") "m⇒"
  , (["A ⊢ B", "C ⊢ D"] ⟶ "A ⇐ D ⊢ B ⇐ C") "m⇐"
  , (["B ⊢ A ⇒ C"]      ⟶ "A ∙ B ⊢ C"    ) "r⇒∙"
  , (["A ∙ B ⊢ C"]      ⟶ "B ⊢ A ⇒ C"    ) "r∙⇒"
  , (["A ⊢ C ⇐ B"]      ⟶ "A ∙ B ⊢ C"    ) "r⇐∙"
  , (["A ∙ B ⊢ C"]      ⟶ "A ⊢ C ⇐ B"    ) "r∙⇐"
  ]

prodAndImpLR2 :: [Rule ConId Int]
prodAndImpLR2 =
  [ (["A ⊢ B", "C ⊢ D"] ⟶ "A ∘ C ⊢ B ∘ D") "m∘"
  , (["A ⊢ B", "C ⊢ D"] ⟶ "B ⇛ C ⊢ A ⇛ D") "m⇛"
  , (["A ⊢ B", "C ⊢ D"] ⟶ "A ⇚ D ⊢ B ⇚ C") "m⇚"
  , (["B ⊢ A ⇛ C"]      ⟶ "A ∘ B ⊢ C"    ) "r⇛∘"
  , (["A ∘ B ⊢ C"]      ⟶ "B ⊢ A ⇛ C"    ) "r∘⇛"
  , (["A ⊢ C ⇚ B"]      ⟶ "A ∘ B ⊢ C"    ) "r⇚∘"
  , (["A ∘ B ⊢ C"]      ⟶ "A ⊢ C ⇚ B"    ) "r∘⇚"
  ]

-- |Rules for (I, L, R) referred to as (I, B, C) in Barker & Shan (2014).
constILR :: [Rule ConId Int]
constILR =
  [ (["A ⊢ B"]                 ⟶ "A ∘ I ⊢ B"            ) "Iᵢ"
  , (["A ∘ I ⊢ B"]             ⟶ "A ⊢ B"                ) "Iₑ"
  , (["A ∙ (B ∘ C) ⊢ D"]       ⟶ "B ∘ ((L ∙ A) ∙ C) ⊢ D") "Lᵢ"
  , (["B ∘ ((L ∙ A) ∙ C) ⊢ D"] ⟶ "A ∙ (B ∘ C) ⊢ D"      ) "Lₑ"
  , (["(A ∘ B) ∙ C ⊢ D"]       ⟶ "A ∘ ((R ∙ B) ∙ C) ⊢ D") "Rᵢ"
  , (["A ∘ ((R ∙ B) ∙ C) ⊢ D"] ⟶ "(A ∘ B) ∙ C ⊢ D"      ) "Rₑ"
  ]
