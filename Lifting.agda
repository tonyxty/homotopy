{-# OPTIONS --safe --without-K #-}
open import Categories.Category

module Lifting {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Data.Product

open Category 𝒞

private
  variable
    a b c d : Obj
    f : a ⇒ b
    g : c ⇒ d
    u : a ⇒ c
    v : b ⇒ d

{-
  a--u->c
  |    ^|
  |   / |
  f  γ  g
  | /   |
  v/    v
  b--v->d
-}

LiftingProblem : a ⇒ b → c ⇒ d → a ⇒ c → b ⇒ d → Set _
LiftingProblem f g u v = CommutativeSquare f u v g where open Definitions 𝒞

LiftingSolution : LiftingProblem f g u v → Set _
LiftingSolution {f = f} {g = g} {u = u} {v = v} _ = ∃[ γ ] (u ≈ γ ∘ f × v ≈ g ∘ γ)

_HasLiftingProperty_ : a ⇒ b → c ⇒ d → Set _
f HasLiftingProperty g = ∀ {u v} → (P : LiftingProblem f g u v) → LiftingSolution P
