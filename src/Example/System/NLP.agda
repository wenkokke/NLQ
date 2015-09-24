------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level            using (zero)
open import Data.Product     using (Σ; _,_; proj₁; proj₂)
open import Data.Traversable using (module RawTraversable)
open import Reflection       using (Name)


module Example.System.NLP where


open import Example.System.Base                public
open import Logic.Grammar                      public
open import Logic.NLP.ResMon.Type         Atom public
open import Logic.NLP.ResMon.Type.Context Atom public
open import Logic.NLP.ResMon.Sequent      Atom public
open import Logic.NLP.ResMon.Base         Atom public
