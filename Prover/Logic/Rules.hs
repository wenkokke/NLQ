module Logic.Rules where


import Prover hiding (Term)
import Logic.Base
import Logic.DSL


-- |Inference rules for the non-associative Lambek calculus.
nl :: [Rule String ConId Int]
nl = axioms ++ focusing ++ prodAndImpLR


-- |Inference rules for the polarised non-associative Lambek calculus.
fnl :: [Rule String ConId Int]
fnl = polarisedAxioms ++ polarisedFocusing ++ prodAndImpLR


-- |Inference rules for the classical non-associative Lambek calculus.
cnl :: [Rule String ConId Int]
cnl = axioms ++ focusing ++ boxAndDia ++ prodAndImpLR ++ plusAndSubLR


-- |Inference rules for the polarised classical non-associative Lambek calculus.
fcnl :: [Rule String ConId Int]
fcnl = polarisedAxioms ++ polarisedFocusing ++ boxAndDia ++ prodAndImpLR
       ++ plusAndSubLR


-- |Inference rules for the Lambek-Grishin calculus.
lg :: [Rule String ConId Int]
lg = axioms ++ focusing ++ boxAndDia ++ prodAndImpLR ++ plusAndSubLR
     ++ grishinIV


-- |Inference rules for the polarised Lambek-Grishin calculus.
flg :: [Rule String ConId Int]
flg = polarisedAxioms ++ polarisedFocusing ++ boxAndDia ++ prodAndImpLR
      ++ plusAndSubLR ++ grishinIV


-- |Inference rules for axioms.
axioms :: [Rule String ConId Int]
axioms =
  [ (( [] ⟶ [ "A" ] ⊢   "A"   ) "ax⁻") { guard = atomA }
  , (( [] ⟶   "B"   ⊢ [ "B" ] ) "ax⁺") { guard = atomB }
  ]
  where
    atomA (Con JFocusL [Con (Atom _) [], _]) = True; atomA _ = False
    atomB (Con JFocusR [_, Con (Atom _) []]) = True; atomB _ = False

-- |Polarised inference rules for axioms.
polarisedAxioms :: [Rule String ConId Int]
polarisedAxioms =
  [ (( [] ⟶ [ "A" ] ⊢   "A"   ) "ax⁻") { guard = atomA }
  , (( [] ⟶   "B"   ⊢ [ "B" ] ) "ax⁺") { guard = atomB }
  ]
  where
    atomA (Con JFocusL [Con (Atom a) [], _]) = isNegativeAtom a; atomA _ = False
    atomB (Con JFocusR [_, Con (Atom b) []]) = isPositiveAtom b; atomB _ = False



-- |Inference rules for focusing and unfocusing.
focusing :: [Rule String ConId Int]
focusing =
  [ ( [   "X"   ⊢   "B"   ] ⟶   "X"   ⊢ [ "B" ] ) "⇁"
  , ( [   "A"   ⊢   "Y"   ] ⟶ [ "A" ] ⊢   "Y"   ) "↽"
  , ( [   "X"   ⊢ [ "B" ] ] ⟶   "X"   ⊢   "B"   ) "⇀"
  , ( [ [ "A" ] ⊢   "Y"   ] ⟶   "A"   ⊢   "Y"   ) "↼"
  ]

-- |Polarised inference rules for focusing and unfocusing.
polarisedFocusing :: [Rule String ConId Int]
polarisedFocusing =
  [ (( [   "X"   ⊢   "B"   ] ⟶   "X"   ⊢ [ "B" ] ) "⇁") { guard = negB }
  , (( [   "A"   ⊢   "Y"   ] ⟶ [ "A" ] ⊢   "Y"   ) "↽") { guard = posA }
  , (( [   "X"   ⊢ [ "B" ] ] ⟶   "X"   ⊢   "B"   ) "⇀") { guard = posB }
  , (( [ [ "A" ] ⊢   "Y"   ] ⟶   "A"   ⊢   "Y"   ) "↼") { guard = negA }
  ]
  where
    posA (Con JFocusL [a, _])            = pos a; posA _ = False
    negB (Con JFocusR [_, b])            = neg b; negB _ = False
    negA (Con JStruct [Con Down [a], _]) = neg a; negA _ = False
    posB (Con JStruct [_, Con Down [b]]) = pos b; posB _ = False


-- |Residuation and monotonicity rules for (□ , ◇)
island :: [Rule String ConId Int]
island =
  [ ([  ◇· "A"   ⊢    "Y"   ] ⟶   ◇  "A"   ⊢     "Y"   ) "◇ᴸ"
  , ([     "X"   ⊢  [ "B" ] ] ⟶   ◇· "X"   ⊢ [ ◇  "B" ]) "◇ᴿ"
  ]


-- |Residuation and monotonicity rules for (□ , ◇)
boxAndDia :: [Rule String ConId Int]
boxAndDia =
  [ ([  ◇· "A"   ⊢    "Y"   ] ⟶   ◇  "A"   ⊢     "Y"   ) "◇ᴸ"
  , ([     "X"   ⊢  [ "B" ] ] ⟶   ◇· "X"   ⊢ [ ◇  "B" ]) "◇ᴿ"
  , ([   [ "A" ] ⊢    "Y"   ] ⟶ [ □  "A" ] ⊢   □· "Y"  ) "□ᴸ"
  , ([     "X"   ⊢ □· "A"   ] ⟶      "X"   ⊢   □  "A"  ) "□ᴿ"
  , ([     "X"   ⊢ □· "Y"   ] ⟶   ◇· "X"   ⊢      "Y"  ) "r□◇"
  , ([  ◇· "X"   ⊢    "Y"   ] ⟶      "X"   ⊢   □· "Y"  ) "r□◇"
  ]


  --  rules for (₀ , ⁰ , ₁ , ¹)
  -- ₀ᴸ  : ∀ {X A}     → LG X ⊢[ A ] → LG [ ₀ A ]⊢ ₀ X
  -- ₀ᴿ  : ∀ {X A}     → LG X ⊢ ₀ · A · → LG X ⊢ · ₀ A ·
  -- ⁰ᴸ  : ∀ {X A}     → LG X ⊢[ A ] → LG [ A ⁰ ]⊢ X ⁰
  -- ⁰ᴿ  : ∀ {X A}     → LG X ⊢ · A · ⁰ → LG X ⊢ · A ⁰ ·
  -- ₁ᴸ  : ∀ {Y A}     → LG ₁ · A · ⊢ Y → LG · ₁ A · ⊢ Y
  -- ₁ᴿ  : ∀ {Y A}     → LG [ A ]⊢ Y → LG ₁ Y ⊢[ ₁ A ]
  -- ¹ᴸ  : ∀ {Y A}     → LG · A · ¹ ⊢ Y → LG · A ¹ · ⊢ Y
  -- ¹ᴿ  : ∀ {Y A}     → LG [ A ]⊢ Y → LG Y ¹ ⊢[ A ¹ ]
  -- r⁰₀ : ∀ {X Y}     → LG X ⊢ Y ⁰ → LG Y ⊢ ₀ X
  -- r₀⁰ : ∀ {X Y}     → LG Y ⊢ ₀ X → LG X ⊢ Y ⁰
  -- r¹₁ : ∀ {X Y}     → LG X ¹ ⊢ Y → LG ₁ Y ⊢ X
  -- r₁¹ : ∀ {X Y}     → LG ₁ Y ⊢ X → LG X ¹ ⊢ Y


-- |Residuation and monotonicity rules for (⇐, ⊗, ⇒)
prodAndImpLR :: [Rule String ConId Int]
prodAndImpLR =
  [ ( [ "A" ·⊗· "B" ⊢ "Y" ]             ⟶ "A" ⊗ "B" ⊢ "Y"             ) "⊗ᴸ"
  , ( [ "X" ⊢ [ "A" ] , "Y" ⊢ [ "B" ] ] ⟶ "X" ·⊗· "Y" ⊢ [ "A" ⊗ "B" ] ) "⊗ᴿ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ [ "A" ⇒ "B" ] ⊢ "X" ·⇒· "Y" ) "⇒ᴸ"
  , ( [ "X" ⊢ "A" ·⇒· "B" ]             ⟶ "X" ⊢ "A" ⇒ "B"             ) "⇒ᴿ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ [ "B" ⇐ "A" ] ⊢ "Y" ·⇐· "X" ) "⇐ᴸ"
  , ( [ "X" ⊢ "B" ·⇐· "A" ]             ⟶ "X" ⊢ "B" ⇐ "A"             ) "⇐ᴿ"

  , ( [ "Y" ⊢ "X" ·⇒· "Z" ]             ⟶ "X" ·⊗· "Y" ⊢ "Z"           ) "r⇒⊗"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ]             ⟶ "Y" ⊢ "X" ·⇒· "Z"           ) "r⊗⇒"
  , ( [ "X" ⊢ "Z" ·⇐· "Y" ]             ⟶ "X" ·⊗· "Y" ⊢ "Z"           ) "r⇐⊗"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ]             ⟶ "X" ⊢ "Z" ·⇐· "Y"           ) "r⊗⇐"
  ]

-- |Residuation and monotonicity rules for (⇚, ⊕, ⇛)
plusAndSubLR :: [Rule String ConId Int]
plusAndSubLR =
  [ ( [ [ "B" ] ⊢ "Y" , [ "A" ] ⊢ "X" ] ⟶ [ "B" ⊕ "A" ] ⊢ "Y" ⊕ "X"   ) "⊕ᴸ"
  , ( [ "X" ⊢ "B" ·⊕· "A" ]             ⟶ "X" ⊢ "B" ⊕ "A"             ) "⊕ᴿ"
  , ( [ "A" ·⇚· "B" ⊢ "X" ]             ⟶ "A" ⇚ "B" ⊢ "X"             ) "⇚ᴸ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ "X" ·⇚· "Y" ⊢ [ "A" ⇚ "B" ] ) "⇚ᴿ"
  , ( [ "B" ·⇛· "A" ⊢ "X" ]             ⟶ "B" ⇛ "A" ⊢ "X"             ) "⇛ᴸ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ "Y" ·⇛· "X" ⊢ [ "B" ⇛ "A" ] ) "⇛ᴿ"

  , ( [ "Z" ·⇚· "X" ⊢ "Y" ]             ⟶ "Z" ⊢ "Y" ·⊕· "X"           ) "r⇚⊕"
  , ( [ "Z" ⊢ "Y" ·⊕· "X" ]             ⟶ "Z" ·⇚· "X" ⊢ "Y"           ) "r⊕⇚"
  , ( [ "Y" ·⇛· "Z" ⊢ "X" ]             ⟶ "Z" ⊢ "Y" ·⊕· "X"           ) "r⇛⊕"
  , ( [ "Z" ⊢ "Y" ·⊕· "X" ]             ⟶ "Y" ·⇛· "Z" ⊢ "X"           ) "r⊕⇛"
  ]


-- |Grishin interaction postulates IV.
grishinIV :: [Rule String ConId Int]
grishinIV =
  [ ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Z" ·⇛· "X" ⊢ "W" ·⇐· "Y"   ) "d⇛⇐"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Z" ·⇛· "Y" ⊢ "X" ·⇒· "W"   ) "d⇛⇒"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Y" ·⇚· "W" ⊢ "X" ·⇒· "Z"   ) "d⇚⇒"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "X" ·⇚· "W" ⊢ "Z" ·⇐· "Y"   ) "d⇚⇐"
  ]
