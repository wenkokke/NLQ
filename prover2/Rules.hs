{-# LANGUAGE RecordWildCards #-}
module Rules where


import Base


data Rule = Rule
  { name       :: String
  , premises   :: [Judgement]
  , conclusion :: Judgement
  }
  deriving (Eq)


instance Show Rule where
  showsPrec _ Rule{..} =
      showString "( "
    . showList premises
    . showString " ⟶ "
    . shows conclusion
    . showString " ) \""
    . showString name
    . showString "\"\n"


infixr 1 ⟶

(⟶) :: [Judgement] -> Judgement -> String -> Rule
(⟶) p c n = Rule { name = n , premises = p , conclusion = c }


rulesLambekGrishin :: [Rule]
rulesLambekGrishin =
  [ ( [] ⟶   "A"   ⊢ [ "A" ] ) "ax⁻"
  , ( [] ⟶ [ "A" ] ⊢   "A"   ) "ax⁺"

    -- rules for (⇐ , ⊗ , ⇒)
  , ( [ "A" ·⊗· "B" ⊢ "Y" ]             ⟶ "A" ⊗ "B" ⊢ "Y"             ) "⊗ᴸ"
  , ( [ "X" ⊢ [ "A" ] , "Y" ⊢ [ "B" ] ] ⟶ "X" ·⊗· "Y" ⊢ [ "A" ⊗ "B" ] ) "⊗ᴿ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ [ "A" ⇒ "B" ] ⊢ "X" ·⇒· "Y" ) "⇒ᴸ"
  , ( [ "X" ⊢ "A" ·⇒· "B" ]             ⟶ "X" ⊢ "A" ⇒ "B"             ) "⇒ᴿ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ [ "B" ⇐ "A" ] ⊢ "Y" ⇐ "X"   ) "⇐ᴸ"
  , ( [ "X" ⊢ "B" ·⇐· "A" ]             ⟶ "X" ⊢ "B" ⇐ "A"             ) "⇐ᴿ"

  , ( [ "Y" ⊢ "X" ·⇒· "Z" ]             ⟶ "X" ·⊗· "Y" ⊢ "Z"           ) "r⇒⊗"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ]             ⟶ "Y" ⊢ "X" ·⇒· "Z"           ) "r⊗⇒"
  , ( [ "X" ⊢ "Z" ·⇐· "Y" ]             ⟶ "X" ·⊗· "Y" ⊢ "Z"           ) "r⇐⊗"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ]             ⟶ "X" ⊢ "Z" ·⇐· "Y"           ) "r⊗⇐"

    -- rules for (⇚ , ⊕ , ⇛)
  , ( [ [ "B" ] ⊢ "Y" , [ "A" ] ⊢ "X" ] ⟶ [ "B" ⊕ "A" ] ⊢ "Y" ⊕ "X"   ) "⊕ᴸ"
  , ( [ "X" ⊢ "B" ·⊕· "A" ]             ⟶ "X" ⊢ "B" ⊕ "A"             ) "⊕ᴿ"
  , ( [ "A" ·⇚· "B" ⊢ "X" ]             ⟶ "A" ⇚ "B" ⊢ "X"             ) "⇚ᴸ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ "X" ·⇚· "Y" ⊢ [ "A" ⇚ "B" ] ) "⇚ᴿ"
  , ( [ "B" ·⇛· "A" ⊢ "X" ]             ⟶ "B" ⇛ "A" ⊢ "X"             ) "⇛ᴸ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ "Y" ·⇛· "X" ⊢ [ "B" ⇛ "A" ] ) "⇛ᴿ"

  , ( [ "Z" ·⇚· "X" ⊢ "Y" ]             ⟶ "Z" ⊢ "Y" ·⊕· "X"           ) "r⇚⊕"
  , ( [ "Z" ⊢ "Y" ·⊕· "X" ]             ⟶ "Z" ·⇚· "X" ⊢ "Y"           ) "r⊕⇚"
  , ( [ "Y" ·⇛· "Z" ⊢ "X" ]             ⟶ "Z" ⊢ "Y" ·⊕· "X"           ) "r⇛⊕"
  , ( [ "Z" ⊢ "Y" ·⊕· "X" ]             ⟶ "Y" ·⇛· "Z" ⊢ "X"           ) "r⊕⇛"

    -- grishin interaction principes
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Z" ·⇛· "X" ⊢ "W" ·⇐· "Y"   ) "d⇛⇐"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Z" ·⇛· "Y" ⊢ "X" ·⇒· "W"   ) "d⇛⇒"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Y" ·⇚· "W" ⊢ "X" ·⇒· "Z"   ) "d⇚⇒"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "X" ·⇚· "W" ⊢ "Z" ·⇐· "Y"   ) "d⇚⇐"
  ]
