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


open import Logic.Type Univ
open import Logic.Judgement (List Type) Type (List Type)
open import Logic.Classical.Unrestricted.LambdaCMinus.Indexed.Base Univ

private
  Generator : Set
  Generator = Stream String × Stream String

  open RawMonadState (StateMonadState Generator)

  genˣ : State Generator String
  genˣ = get >>= (λ {((x ∷ xs) , ks) → put (♭ xs , ks) >> return x})

  genᵏ : State Generator String
  genᵏ = get >>= (λ {(xs , (k ∷ ks)) → put (xs , ♭ ks) >> return k})


  infixr 5 _∙_

  _∙_ : String → String → String
  xs ∙ ys = xs ++ " " ++ ys

  parens : String → String
  parens str = "(" ++ str ++ ")"


  mutual
    genShow : ∀ {Γ A Δ}
            → (namesˣ : Vec String (length Γ))
            → (namesᵏ : Vec String (length Δ))
            → λC⁻ Γ ⊢[ A ] Δ
            → State Generator String
    genShow nˣ nᵏ (ax  x  ) = return $ lookup x nˣ
    genShow nˣ nᵏ (⇒ᵢ  f  ) = genˣ >>= λ x
                            → genShow (x ∷ nˣ) nᵏ f >>= λ f
                            → return
                            $ parens ("λ" ∙ x ∙ "→" ∙ f)
    genShow nˣ nᵏ (⇒ₑ  f g) = genShow nˣ nᵏ f >>= λ f
                            → genShow nˣ nᵏ g >>= λ g
                            → return
                            $ parens (f ∙ g)
    genShow nˣ nᵏ (raa f  ) = genᵏ >>= λ α
                            → genShow′ nˣ (α ∷ nᵏ) f >>= λ f
                            → return
                            $ "C⁻" ++ (parens ("λ" ∙ α ∙ "→" ∙ f))
    genShow nˣ nᵏ (-ᵢ  f g) = genShow         nˣ  nᵏ f >>= λ f
                            → genShow′ ("□" ∷ nˣ) nᵏ g >>= λ g
                            → return
                            $ parens (f ∙ "," ∙ g)
    genShow nˣ nᵏ (-ₑ  f g) = genˣ >>= λ x
                            → genᵏ >>= λ α
                            → genShow      nˣ       nᵏ  f >>= λ f
                            → genShow (x ∷ nˣ) (α ∷ nᵏ) g >>= λ g
                            → return
                            $ parens ("let" ∙ (parens (x ∙ "," ∙ α)) ∙ "=" ∙ f ∙ "in" ∙ g)
    genShow nˣ nᵏ (⊗ᵢ  f g) = genShow nˣ nᵏ f >>= λ f
                            → genShow nˣ nᵏ g >>= λ g
                            → return
                            $ parens (f ∙ "," ∙ g)
    genShow nˣ nᵏ (⊗ₑ  f g) = genˣ >>= λ x
                            → genˣ >>= λ y
                            → genShow          nˣ  nᵏ f >>= λ f
                            → genShow (x ∷ y ∷ nˣ) nᵏ g >>= λ g
                            → return
                            $ parens ("case" ∙ f ∙ "of" ∙ (parens (x ∙ "," ∙ y)) ∙ "→" ∙ g)


    genShow′ : ∀ {Γ Δ}
             → (namesˣ : Vec String (length Γ))
             → (namesᵏ : Vec String (length Δ))
             → λC⁻ Γ ⊢ Δ
             → State Generator String
    genShow′ nˣ nᵏ (⇒ₑᵏ α f) = genShow nˣ nᵏ f >>= λ f
                             → return $ lookup α nᵏ ∙ f


  namesˣ : Stream String
  namesˣ = map (λ n → "x" ++ showℕ n) (iterate suc 0)
  namesᵏ : Stream String
  namesᵏ = map (λ n → "k" ++ showℕ n) (iterate suc 0)


show : ∀ {J} → λC⁻ J → String
show {Γ ⊢      Δ} f = proj₁ $
  genShow′ (take (length Γ) namesˣ)   (take (length Δ) namesᵏ) f
          ((drop (length Γ) namesˣ) , (drop (length Δ) namesᵏ))
show {Γ ⊢[ _ ] Δ} f = proj₁ $
  genShow  (take (length Γ) namesˣ)   (take (length Δ) namesᵏ) f
          ((drop (length Γ) namesˣ) , (drop (length Δ) namesᵏ))
