------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Category.Monad.State
open import Coinduction      using (♭)
open import Data.Bool        using (true)
open import Data.List        using (length)
open import Data.Nat         using (suc)
open import Data.Nat.Show    using (show)
open import Data.Product     using (proj₁)
open import Data.String      using (String; _++_)
open import Data.Stream as S using (Stream; _∷_; map; iterate; take; drop)
open import Data.Vec    as V using (Vec; _∷_; []; map; lookup)
open import Function         using (_∘_)
open import Logic.ToLaTeX


module Logic.Intuitionistic.Unrestricted.Lambda.Indexed.ToLaTeX {ℓ} (Atom : Set ℓ) where


open import Logic.Intuitionistic.Unrestricted.Lambda.Type              Atom
open import Logic.Intuitionistic.Unrestricted.Lambda.Type.ToLaTeX      Atom
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement         Atom
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement.ToLaTeX Atom
open import Logic.Intuitionistic.Unrestricted.Lambda.Indexed.Base      Atom
open RawMonadState (StateMonadState (Stream String))


instance
  toLaTeXTerm : ∀ {Γ A} → Vec String (length Γ) → Λ Γ ⊢ A → String
  toLaTeXTerm xs f = proj₁ (go′ (V.map (λ x → "\\text{" ++ x ++ "}") xs) f names)
    where
      fresh : State (Stream String) String
      fresh = get >>= λ {(x ∷ xs) → put (♭ xs) >> return x}

      names : Stream String
      names = S.map (λ n → "x_{" ++ show n ++ "}") (iterate suc 0)

      go′ : ∀ {Γ A} → Vec String (length Γ) → Λ Γ ⊢ A → State (Stream String) String
      go′ xs (ax x)   = return (lookup x xs)
      go′ xs (⇒ᵢ f)   = fresh         >>= λ x
                      → go′ (x ∷ xs) f >>= λ f
                      → return (parens true ("\\lambda" ∙ x ∙ "\\mathbin{\\to}" ∙ f))
      go′ xs (⇒ₑ f g) = go′ xs f >>= λ f
                      → go′ xs g >>= λ g
                      → return (parens true (f ∙ "\\;" ∙ g))
      go′ xs (⊗ᵢ f g) = go′ xs f >>= λ f
                      → go′ xs g >>= λ g
                      → return (parens true (f ∙ "\\mathbin{,}" ∙ g))
      go′ xs (⊗ₑ f g) = fresh              >>= λ x
                      → fresh              >>= λ y
                      → go′          xs  f >>= λ f
                      → go′ (x ∷ y ∷ xs) g >>= λ g
                      → return ( parens true
                               ( "\\mathbf{case}\\;"
                               ∙ f
                               ∙ "\\;\\mathbf{of}\\;"
                               ∙ parens true ( x
                                             ∙ "\\mathbin{,}"
                                             ∙ y)
                               ∙ "\\mathbin{\\to}"
                               ∙ g))
