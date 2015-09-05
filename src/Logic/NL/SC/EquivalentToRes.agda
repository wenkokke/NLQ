------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Logic.NL.SC.EquivalentToRes {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type                 Atom
open import Logic.NL.Res                  Atom renaming (_⊢NL_ to _⊢R_)
open import Logic.NL.SC.Structure         Atom
open import Logic.NL.SC.Structure.Context Atom
open import Logic.NL.SC.Sequent         Atom
open import Logic.NL.SC.Base              Atom renaming (_⊢NL_ to _⊢SC_)


⌊_⌋ : Structure → Type
⌊ · A ·  ⌋  = A
⌊ Γ , Δ  ⌋  = ⌊ Γ ⌋ ⊗ ⌊ Δ ⌋


⌊⌋-over-[] : (Γ : Context) {A B : Type}
           → ⌊ Γ [ · A ⊗ B · ] ⌋ ≡ ⌊ Γ [ · A · , · B · ] ⌋
⌊⌋-over-[] []       {A} {B} = refl
⌊⌋-over-[] (_ ,> Γ) {A} {B} rewrite ⌊⌋-over-[] Γ {A} {B} = refl
⌊⌋-over-[] (Γ <, _) {A} {B} rewrite ⌊⌋-over-[] Γ {A} {B} = refl


cutIn′  : ∀ {Γ Δ Δ′ A} → ⌊ Δ ⌋ ⊢R ⌊ Δ′ ⌋ → ⌊ Γ [ Δ′ ] ⌋ ⊢R A → ⌊ Γ [ Δ ] ⌋ ⊢R A
cutIn′ {Γ = []      } f g = cut f g
cutIn′ {Γ = _ ,> Γ  } f g = r⇒⊗ (cutIn′ {Γ = Γ} f (r⊗⇒ g))
cutIn′ {Γ = Γ <, _  } f g = r⇐⊗ (cutIn′ {Γ = Γ} f (r⊗⇐ g))


from : ∀ {Γ A} → Γ ⊢SC A → ⌊ Γ ⌋ ⊢R A
from  ax                = ax
from (cut {Δ = Γ} f g)  = cutIn′ {Γ = Γ} (from f) (from g)
from (⇒L  {Γ = Γ} f g)  = cutIn′ {Γ = Γ} (r⇐⊗ (cut (from g) (r⊗⇐ (r⇒⊗ ax)))) (from f)
from (⇐L  {Γ = Γ} f g)  = cutIn′ {Γ = Γ} (r⇒⊗ (cut (from g) (r⊗⇒ (r⇐⊗ ax)))) (from f)
from (⊗R          f g)  = m⊗′ (from f) (from g)
from (⇒R          f)    = r⊗⇒ (from f)
from (⇐R          f)    = r⊗⇐ (from f)
from (⊗L  {Γ = Γ} {A} {B} f)    rewrite ⌊⌋-over-[] Γ {A} {B} = from f


to : ∀ {A B} → A ⊢R B → · A · ⊢SC B
to  ax       = ax
to (cut f g) = cut {Δ = []} (to f) (to g)
to (r⇒⊗ f)   = ⊗L {Γ = []} (cut {Δ = _ ,> []} (to f) (⇒L {Γ = []} ax ax))
to (r⊗⇒ f)   = ⇒R (cut {Δ = []} (⊗R ax ax) (to f))
to (r⇐⊗ f)   = ⊗L {Γ = []} (cut {Δ = [] <, _} (to f) (⇐L {Γ = []} ax ax))
to (r⊗⇐ f)   = ⇐R (cut {Δ = []} (⊗R ax ax) (to f))
