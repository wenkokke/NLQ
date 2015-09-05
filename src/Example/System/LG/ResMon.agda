------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level            using (zero)
open import Data.Product     using (Σ; _,_; proj₁; proj₂)
open import Data.Traversable using (module RawTraversable)
open import Reflection       using (Name)


module Example.System.LG.ResMon where


open import Example.System.Base                        public
open import Logic.Grammar                              public
open import Logic.LG.ResMon             Atom           public
open import Logic.LG.ResMon.ProofSearch Atom _≟-Atom_  public
open import Logic.LG.ResMon.ToAgda      Atom Bool ⟦_⟧ᴬ public
