------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level        using (Lift; lift)
open import Function     using (id; flip)
open import Data.Product using (_×_; _,_; map; curry; uncurry; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)


module Logic.NLIBC.ResMon.ToAgda
  {a ℓ} (Atom : Set a) (⟦_⟧ᵁ : Atom → Set ℓ) where


open import Logic.Translation
open import Logic.NLIBC.Type             Atom as NLT
open import Logic.NLIBC.ResMon.Judgement Atom as NLJ
open import Logic.NLIBC.ResMon.Base      Atom as NLB


private
  infix 3 ⟦_⟧ᵀ ⟦_⟧ᴶ [_]

  ⟦_⟧ᵀ : Type → Set ℓ
  ⟦ el  x ⟧ᵀ = ⟦ x ⟧ᵁ
  ⟦ x ⊗ y ⟧ᵀ = ⟦ x ⟧ᵀ × ⟦ y ⟧ᵀ
  ⟦ x ⇒ y ⟧ᵀ = ⟦ x ⟧ᵀ → ⟦ y ⟧ᵀ
  ⟦ y ⇐ x ⟧ᵀ = ⟦ x ⟧ᵀ → ⟦ y ⟧ᵀ
  ⟦ x ∘ y ⟧ᵀ = ⟦ x ⟧ᵀ × ⟦ y ⟧ᵀ
  ⟦ x ⇨ y ⟧ᵀ = ⟦ x ⟧ᵀ → ⟦ y ⟧ᵀ
  ⟦ y ⇦ x ⟧ᵀ = ⟦ x ⟧ᵀ → ⟦ y ⟧ᵀ
  ⟦ I     ⟧ᵀ = Lift ⊤
  ⟦ B     ⟧ᵀ = Lift ⊤
  ⟦ C     ⟧ᵀ = Lift ⊤

  ⟦_⟧ᴶ : Judgement → Set ℓ
  ⟦ x ⊢ y ⟧ᴶ = ⟦ x ⟧ᵀ → ⟦ y ⟧ᵀ

  [_] : ∀ {J} → NL J → ⟦ J ⟧ᴶ
  [ ax      ] = id
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
  [ mB      ] = id
  [ mC      ] = id
  [ Iᵢ  f   ]   x      = [ f ] (x , _)
  [ Iₑ  f   ] ( x , _) = [ f ] x
  [ Bᵢ  f   ] ( x ,      y  , z) = [ f ] (y , (_ , x) , z)
  [ Bₑ  f   ] ( y , (_ , x) , z) = [ f ] (x , (y , z))
  [ Cᵢ  f   ] ((x ,      y) , z) = [ f ] (x , (_ , y) , z)
  [ Cₑ  f   ] ( x , (_ , y) , z) = [ f ] ((x , y) , z)


NLIBC→λΠ : Translation Type (Set ℓ) NL_ id
NLIBC→λΠ = record { ⟦_⟧ᵀ = ⟦_⟧ᵀ ; ⟦_⟧ᴶ = ⟦_⟧ᴶ ; [_] = [_] }
