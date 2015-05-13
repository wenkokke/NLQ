------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level        using (Lift; lift)
open import Function     using (id; flip; _∘_)
open import Data.Product using (_×_; _,_; map; curry; uncurry; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)


module Logic.Intuitionistic.Ordered.InSitu.ToAgda {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (⟦_⟧ᵁ : Univ → Set ℓ₂) where


open import Logic.Translation
open import Logic.Intuitionistic.Ordered.InSitu.Type      Univ as NLT
open import Logic.Intuitionistic.Ordered.InSitu.Judgement Univ as NLJ
open import Logic.Intuitionistic.Ordered.InSitu.Base      Univ as NLB


private
  ⟦_⟧ᵀ : Type → Set ℓ₂
  ⟦ el  A ⟧ᵀ = ⟦ A ⟧ᵁ
  ⟦ ◇   A ⟧ᵀ = ⟦ A ⟧ᵀ
  ⟦ □   A ⟧ᵀ = ⟦ A ⟧ᵀ
  ⟦ A ⊗ B ⟧ᵀ = ⟦ A ⟧ᵀ × ⟦ B ⟧ᵀ
  ⟦ A ⇒ B ⟧ᵀ = ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ
  ⟦ B ⇐ A ⟧ᵀ = ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ
  ⟦ A ∘ B ⟧ᵀ = ⟦ A ⟧ᵀ × ⟦ B ⟧ᵀ
  ⟦ A ⇨ B ⟧ᵀ = ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ
  ⟦ B ⇦ A ⟧ᵀ = ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ
  ⟦ I     ⟧ᵀ = Lift ⊤
  ⟦ L     ⟧ᵀ = Lift ⊤
  ⟦ R     ⟧ᵀ = Lift ⊤

  ⟦_⟧ᴶ : Judgement → Set ℓ₂
  ⟦ A ⊢ B ⟧ᴶ = ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ

  [_] : ∀ {J} → NL J → ⟦ J ⟧ᴶ
  [ ax      ] = id
  [ m□  f   ] = [ f ]
  [ m◇  f   ] = [ f ]
  [ r□◇ f   ] = [ f ]
  [ r◇□ f   ] = [ f ]
  [ m⊗  f g ] = map [ f ] [ g ]
  [ m⇒  f g ] h x = [ g ] (h ([ f ] x))
  [ m⇐  f g ] h x = [ f ] (h ([ g ] x))
  [ r⇒⊗ f   ] = uncurry (flip [ f ])
  [ r⊗⇒ f   ] = flip (curry [ f ])
  [ r⇐⊗ f   ] = uncurry [ f ]
  [ r⊗⇐ f   ] = curry [ f ]
  [ m∘  f g ] = map [ f ] [ g ]
  [ m⇨  f g ] h x = [ g ] (h ([ f ] x))
  [ m⇦  f g ] h x = [ f ] (h ([ g ] x))
  [ r⇨∘ f   ] = uncurry (flip [ f ])
  [ r∘⇨ f   ] = flip (curry [ f ])
  [ r⇦∘ f   ] = uncurry [ f ]
  [ r∘⇦ f   ] = curry [ f ]
  [ mI      ] = id
  [ mL      ] = id
  [ mR      ] = id
  [ Iᵢ  f   ]   x      = [ f ] ( x , _ )
  [ Iₑ  f   ] ( x , _) = [ f ]   x
  [ Lᵢ  f   ] ( x ,      y  , z) = [ f ] ( y , (_ , x) , z )
  [ Lₑ  f   ] ( y , (_ , x) , z) = [ f ] ( x , (y , z))
  [ Rᵢ  f   ] ((x ,      y) , z) = [ f ] ( x , (_ , y) , z )
  [ Rₑ  f   ] ( x , (_ , y) , z) = [ f ] ((x , y) , z )


InSitu→λΠ : Translation Type (Set ℓ₂) NL_ id
InSitu→λΠ = record { ⟦_⟧ᵀ = ⟦_⟧ᵀ ; ⟦_⟧ᴶ = ⟦_⟧ᴶ ; [_] = [_] }
