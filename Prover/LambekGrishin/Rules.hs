module LambekGrishin.Rules where


import Prover hiding (Term)
import LambekGrishin.Base
import LambekGrishin.DSL


lambek :: [Rule String ConId Int]
lambek =
  axioms ++ focusing ++ prodAndImpLR


lambekGrishin :: [Rule String ConId Int]
lambekGrishin =
  axioms ++ focusing ++ prodAndImpLR ++ plusAndSubLR ++ grishinIV


polarisedLambekGrishin :: [Rule String ConId Int]
polarisedLambekGrishin =
  polarisedAxioms ++ polarisedFocusing ++ prodAndImpLR ++ plusAndSubLR ++ grishinIV


polarisedAxioms :: [Rule String ConId Int]
polarisedAxioms =
  [ (( [] ⟶ [ "A" ] ⊢   "A"   ) "ax⁺") { guard = atomA }
  , (( [] ⟶   "B"   ⊢ [ "B" ] ) "ax⁻") { guard = atomB }
  ]
  where
    atomA (Con JFocusL [Con (Atom a) [], _]) = isPositiveAtom a; atomA _ = False
    atomB (Con JFocusR [_, Con (Atom b) []]) = isNegativeAtom b; atomB _ = False


polarisedFocusing :: [Rule String ConId Int]
polarisedFocusing =
  [ (( [   "A"   ⊢   "Y"   ] ⟶ [ "A" ] ⊢   "Y"   ) "↽") { guard = posA }
  , (( [   "X"   ⊢   "B"   ] ⟶   "X"   ⊢ [ "B" ] ) "⇁") { guard = negB }
  , (( [ [ "A" ] ⊢   "Y"   ] ⟶   "A"   ⊢   "Y"   ) "↼") { guard = negA }
  , (( [   "X"   ⊢ [ "B" ] ] ⟶   "X"   ⊢   "B"   ) "⇀") { guard = posB }
  ]
  where
    posA (Con JFocusL [a, _])            = pos a; posA _ = False
    negB (Con JFocusR [_, b])            = neg b; negB _ = False
    negA (Con JStruct [Con Down [a], _]) = neg a; negA _ = False
    posB (Con JStruct [_, Con Down [b]]) = pos b; posB _ = False


axioms :: [Rule String ConId Int]
axioms =
  [ (( [] ⟶   "B"   ⊢ [ "B" ] ) "ax⁻") { guard = atomB }
  , (( [] ⟶ [ "A" ] ⊢   "A"   ) "ax⁺") { guard = atomA }
  ]
  where
    atomB (Con JFocusR [_, Con (Atom _) []]) = True; atomB _ = False
    atomA (Con JFocusL [Con (Atom _) [], _]) = True; atomA _ = False


focusing :: [Rule String ConId Int]
focusing =
  [ ( [   "X"   ⊢   "B"   ] ⟶   "X"   ⊢ [ "B" ] ) "⇁"
  , ( [   "A"   ⊢   "Y"   ] ⟶ [ "A" ] ⊢   "Y"   ) "↽"
  , ( [   "X"   ⊢ [ "B" ] ] ⟶   "X"   ⊢   "B"   ) "⇀"
  , ( [ [ "A" ] ⊢   "Y"   ] ⟶   "A"   ⊢   "Y"   ) "↼"
  ]


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


grishinIV :: [Rule String ConId Int]
grishinIV =
  [ ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Z" ·⇛· "X" ⊢ "W" ·⇐· "Y"   ) "d⇛⇐"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Z" ·⇛· "Y" ⊢ "X" ·⇒· "W"   ) "d⇛⇒"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Y" ·⇚· "W" ⊢ "X" ·⇒· "Z"   ) "d⇚⇒"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "X" ·⇚· "W" ⊢ "Z" ·⇐· "Y"   ) "d⇚⇐"
  ]
