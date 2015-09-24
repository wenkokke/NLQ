# Extended Categorial Grammar
``` hidden
module extended_categorial_grammar where
```



## `LG`: The Lambek-Grishin calculus

[compute](Example/System/LG/ResMon.agda
  "asSyntaxDeclOf (quote Type) (quote _⊕_ ∷ quote _⇚_ ∷ quote _⇛_ ∷ [])")

[compute](Example/System/LG/ResMon.agda
  "asMathParOf (quote LG_)
    ( quote m⊕  ∷ quote m⇛  ∷ quote m⇚
    ∷ quote r⇛⊕ ∷ quote r⊕⇛ ∷ quote r⊕⇚ ∷ quote r⇚⊕
    ∷ quote d⇛⇐ ∷ quote d⇛⇒ ∷ quote d⇚⇒ ∷ quote d⇚⇐ ∷ [])")

[compute](Example/System/LG/Pol.agda
  "asSyntaxDecl′ (quote Structure⁺) true (\"Γ⁺\" ∷ \"Δ⁺\" ∷ [])
    (quote Structure._⇚_ ∷ quote Structure._⇛_ ∷ [])")

[compute](Example/System/LG/Pol.agda
  "asSyntaxDecl′ (quote Structure⁻) true (\"Γ⁻\" ∷ \"Δ⁻\" ∷ [])
    (quote Structure._⊕_ ∷ [])")

[compute](Example/System/LG/Pol.agda
  "asMathParOf (quote fLG_)
    ( quote ⊕L ∷ quote ⊕R ∷ quote ⇚L ∷ quote ⇚R ∷ quote ⇛L ∷ quote ⇛R
    ∷ quote r⇛⊕ ∷ quote r⊕⇛ ∷ quote r⊕⇚ ∷ quote r⇚⊕
    ∷ quote d⇛⇐ ∷ quote d⇛⇒ ∷ quote d⇚⇒ ∷ quote d⇚⇐ ∷ [])")



## `NL`~`IBC`~: Quantifier raising as structural rule


[compute](Example/System/NLIBC.agda
  "asSyntaxDecl (quote Type)")

[compute](Example/System/NLIBC.agda
  "asSyntaxDecl (quote Structure)")

[compute](Example/System/NLIBC.agda
  "asSyntaxDecl′ (quote Sequent) false (\"I\" ∷ \"J\" ∷ []) (quote _⊢_ ∷ [])")

[compute](Example/System/NLIBC.agda
  "asSyntaxDecl (quote Context)")

[compute](Example/System/NLIBC.agda
  "asMathParOf (quote NL_) ( quote ax
   ∷ quote ⇒L ∷ quote ⇒R ∷ quote ⇐L ∷ quote ⇐R
   ∷ quote ⇨L ∷ quote ⇨R ∷ quote ⇦L ∷ quote ⇦R
   ∷ quote Iᵢ ∷ quote Iₑ ∷ quote Bᵢ ∷ quote Bₑ ∷ quote Cᵢ ∷ quote Cₑ ∷ [])")


### Derived rules


[compute](Example/System/NLIBC.agda
  "asSyntaxDecl (quote Context₁)")

[compute](Example/System/NLIBC.agda
  "asMathParOf (quote NL_) (quote ⇦Lλ ∷ quote ⇨Rλ ∷ [])")


### Gapping as non-logical axiom

[compute](Example/System/NLIBC.agda
  "asMathParOf (quote NL_) (quote ⇨RgL ∷ quote ⇨RgR ∷ [])")


## `NL◇□`: Extraction, infixation, and gapping


### Infixation

[compute](Example/System/NLP.agda
  "asSyntaxDeclOf (quote Type) (quote ◇_ ∷ quote □_ ∷ [])")

[compute](Example/System/NLP.agda
  "asMathParOf (quote NL_) (quote m□ ∷ quote m◇ ∷ quote r□◇ ∷ quote r◇□ ∷ [])")

[compute](Example/System/NLP.agda
  "asMathParOf (quote NL_) (quote iRR ∷ quote iLR ∷ quote iLL ∷ quote iRL ∷ [])")


### Extraction

[compute](Example/System/NLP.agda
  "asSyntaxDeclOf (quote Type) (quote ◆_ ∷ quote ■_ ∷ [])")

[compute](Example/System/NLP.agda
  "asMathParOf (quote NL_) (quote eRR ∷ quote eLR ∷ quote eLL ∷ quote eRL ∷ [])")


### Quantifier raising

[compute](Example/System/NLP.agda
  "asSyntaxDeclOf (quote Type)
    (quote L ∷ quote R ∷ quote ⬗_ ∷ quote ◨_ ∷ quote ⬖_ ∷ quote ◧_ ∷ [])")

[compute](Example/System/NLP.agda
  "asMathParOf (quote NL_)
    ( quote ↓RR ∷ quote ↓LR ∷ quote ↓LL ∷ quote ↓RL
    ∷ quote ↑RR ∷ quote ↑LR ∷ quote ↑LL ∷ quote ↑RL
    ∷ [])")


<!--

### Choice

[compute](Example/System/NLP.agda
  "asSyntaxDeclOf (quote Type) (quote _&_ ∷ [])")

[compute](Example/System/NLP.agda
  "asMathParOf (quote NL_) (quote &L₁ ∷ quote &L₂ ∷ quote &R ∷ [])")
-->


## Scope islands

[compute](Example/System/NLP.agda
  "asSyntaxDeclOf (quote Type) (quote Type.⟨_⟩ ∷ [])")

[compute](Example/System/NLP.agda
  "asMathParOf (quote NL_) (quote m⟨⟩ ∷ [])")
