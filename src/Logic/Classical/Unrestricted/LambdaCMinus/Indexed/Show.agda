------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function             using (_$_)
open import Coinduction          using (♭)
open import Category.Monad.State using (State; StateMonadState; module RawMonadState; RawMonadState)
open import Data.List            using (List; length) renaming ([] to ∅; _∷_ to _,_)
open import Data.Nat             using (suc)
open import Data.Nat.Show        renaming (show to showℕ)
open import Data.Stream          using (Stream; _∷_; iterate; map; take; drop)
open import Data.String          using (String; _++_)
open import Data.Product         using (_×_; _,_; proj₁)
open import Data.Vec             using (Vec; _∷_; []; lookup; tail)


module Logic.Classical.Unrestricted.LambdaCMinus.Indexed.Show {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Unrestricted.LambdaCMinus.Type         Univ
open import Logic.Classical.Unrestricted.LambdaCMinus.Judgement    Univ
open import Logic.Classical.Unrestricted.LambdaCMinus.Indexed.Base Univ

private
  Generator : Set
  Generator = Stream String × Stream String

  open RawMonadState (StateMonadState Generator)

  genˣ : State Generator String
  genˣ = get >>= (λ {((x ∷ xs) , ks) → put (♭ xs , ks) >> return x})
  genᵏ : State Generator String
  genᵏ = get >>= (λ {(xs , (k ∷ ks)) → put (xs , ♭ ks) >> return k})

  namesˣ : Stream String
  namesˣ = map (λ n → "x" ++ showℕ n) (iterate suc 0)
  namesᵏ : Stream String
  namesᵏ = map (λ n → "k" ++ showℕ n) (iterate suc 0)


  infixr 5 _∙_
  _∙_ : String → String → String
  xs ∙ ys = xs ++ " " ++ ys

  parens : String → String
  parens str = "(" ++ str ++ ")"


  showTerm′ : ∀ {J} (namesˣ : Vec String (length (ante J)))
                    (namesᵏ : Vec String (length (succ J)))
            → λC⁻ J → State Generator String
  showTerm′ nˣ nᵏ (ax  x  ) = return $ lookup x nˣ
  showTerm′ nˣ nᵏ (⇒ᵢ  f  ) = genˣ >>= λ x
                            → showTerm′ (x ∷ nˣ) nᵏ f >>= λ f
                            → return
                            $ parens ("λ" ∙ x ∙ "→" ∙ f)
  showTerm′ nˣ nᵏ (⇒ₑ  f g) = showTerm′ nˣ nᵏ f >>= λ f
                            → showTerm′ nˣ nᵏ g >>= λ g
                            → return
                            $ parens (f ∙ g)
  showTerm′ nˣ nᵏ (raa f  ) = genᵏ >>= λ α
                            → showTerm′ nˣ (α ∷ nᵏ) f >>= λ f
                            → return
                            $ "C⁻" ++ (parens ("λ" ∙ α ∙ "→" ∙ f))
  showTerm′ nˣ nᵏ (⇒ₑᵏ α f) = showTerm′ nˣ nᵏ f >>= λ f
                            → return $ lookup α nᵏ ∙ f
  showTerm′ nˣ nᵏ (-ᵢ  f g) = showTerm′         nˣ  nᵏ f >>= λ f
                            → showTerm′ ("□" ∷ nˣ) nᵏ g >>= λ g
                            → return
                            $ parens (f ∙ "," ∙ g)
  showTerm′ nˣ nᵏ (-ₑ  f g) = genˣ >>= λ x
                            → genᵏ >>= λ α
                            → showTerm′      nˣ       nᵏ  f >>= λ f
                            → showTerm′ (x ∷ nˣ) (α ∷ nᵏ) g >>= λ g
                            → return
                            $ parens ("let" ∙ (parens (x ∙ "," ∙ α)) ∙ "=" ∙ f ∙ "in" ∙ g)
  showTerm′ nˣ nᵏ (⊗ᵢ  f g) = showTerm′ nˣ nᵏ f >>= λ f
                            → showTerm′ nˣ nᵏ g >>= λ g
                            → return
                            $ parens (f ∙ "," ∙ g)
  showTerm′ nˣ nᵏ (⊗ₑ  f g) = genˣ >>= λ x
                            → genˣ >>= λ y
                            → showTerm′          nˣ  nᵏ f >>= λ f
                            → showTerm′ (x ∷ y ∷ nˣ) nᵏ g >>= λ g
                            → return
                            $ parens ("case" ∙ f ∙ "of" ∙ (parens (x ∙ "," ∙ y)) ∙ "→" ∙ g)



-- Version of |showTerm| which allows the user to submit a vector of
-- top-level names.
showTermWith : ∀ {J}
             → (namesˣ : Vec String (length (ante J)))
             → (namesᵏ : Vec String (length (succ J)))
             → λC⁻ J → String
showTermWith nˣ nᵏ f = proj₁ (showTerm′ nˣ nᵏ f (namesˣ , namesᵏ))

-- Version of |showTerm| which automatically names the top-level constructs.
showTerm : ∀ {J} → λC⁻ J → String
showTerm {J} f = proj₁ (showTerm′ nˣ nᵏ f (drop |Γ| namesˣ , drop |Δ| namesᵏ))
  where
    |Γ| = length (ante J)
    |Δ| = length (succ J)
    nˣ  = take |Γ| namesˣ
    nᵏ  = take |Δ| namesᵏ
