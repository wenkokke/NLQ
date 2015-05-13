------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Category.Monad.State
open import Coinduction   using (♭)
open import Data.Bool     using (true)
open import Data.List     using (length)
open import Data.Nat      using (suc)
open import Data.Nat.Show using (show)
open import Data.Product  using (proj₁)
open import Data.String   using (String; _++_)
open import Data.Stream   using (Stream; _∷_; map; iterate; take; drop)
open import Data.Vec      using (Vec; _∷_; []; lookup)
open import Function      using (_∘_)
open import Logic.ToLaTeX


module Logic.Intuitionistic.Unrestricted.Lambda.Indexed.ToLaTeX {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Unrestricted.Lambda.Type              Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Type.ToLaTeX      Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement         Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement.ToLaTeX Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Indexed.Base      Univ
open RawMonadState (StateMonadState (Stream String))

instance
  LambdaToLaTeX : ∀ {J} {{UnivToLaTeX : ToLaTeX Univ}} → ToLaTeX (Λ J)
  LambdaToLaTeX = record { toLaTeXPrec = λ _ f → go f }
    where
      fresh : State (Stream String) String
      fresh = get >>= λ {(x ∷ xs) → put (♭ xs) >> return x}

      names : Stream String
      names = map (λ n → "x" ++ show n) (iterate suc 0)

      go′ : ∀ {Γ A} → Vec String (length Γ) → Λ Γ ⊢ A → State (Stream String) String
      go′ xs (ax x)   = return (lookup x xs)
      go′ xs (⇒ᵢ f)   = fresh         >>= λ x
                      → go′ (x ∷ xs) f >>= λ f
                      → return (parens true ("λ" ∙ x ∙ "→" ∙ f))
      go′ xs (⇒ₑ f g) = go′ xs f >>= λ f
                      → go′ xs g >>= λ g
                      → return (parens true (f ∙ g))
      go′ xs (⊗ᵢ f g) = go′ xs f >>= λ f
                      → go′ xs g >>= λ g
                      → return (parens true (f ∙ "," ∙ g))
      go′ xs (⊗ₑ f g) = fresh             >>= λ x
                      → fresh             >>= λ y
                      → go′          xs  f >>= λ f
                      → go′ (x ∷ y ∷ xs) g >>= λ g
                      → return (parens true
                               ("case" ∙ f ∙ "of" ∙ parens true (x ∙ "," ∙ y) ∙ "→" ∙ g))

      go : ∀ {J} → Λ J → String
      go {Γ ⊢ _} f = proj₁ (go′ (take (length Γ) names) f (drop (length Γ) names))
