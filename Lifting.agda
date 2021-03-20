{-# OPTIONS --safe --cubical --without-K #-}
open import Cubical.Categories.Category.Base

module Lifting {ℓ ℓ'} (C : Precategory ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma.Base
open import Cubical.HITs.PropositionalTruncation.Base

open Precategory C

-- the notions can be defined for precategories, but is probably only useful when C is a category.

private
  variable
    a b c d : ob
    f : Hom[ a , b ]
    g : Hom[ c , d ]
    u : Hom[ a , c ]
    v : Hom[ b , d ]

{-
  a--u->c
  |    ^|
  |   / |
  f  γ  g
  | /   |
  v/    v
  b--v->d
-}

LiftingProblem : Hom[ a , b ] → Hom[ c , d ] → Hom[ a , c ] → Hom[ b , d ] → Type _
LiftingProblem f g u v = f ⋆ v ≡ u ⋆ g

LiftingSolution : LiftingProblem f g u v → Type _
LiftingSolution {f = f} {g = g} {u = u} {v = v} _ = Σ[ γ ∈ _ ] ((u ≡ f ⋆ γ) × (v ≡ γ ⋆ g))

_HasLiftingProperty_ : Hom[ a , b ] → Hom[ c , d ] → Type _
f HasLiftingProperty g = ∀ {u v} → (P : LiftingProblem f g u v) → ∥ LiftingSolution P ∥
