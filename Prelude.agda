{-# OPTIONS --safe --cubical --without-K #-}
open import Cubical.Categories.Category.Base

module Prelude {ℓ ℓ'} (C : Precategory ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open Precategory C

ClassOfMorphism : (p : Level) → Type _
ClassOfMorphism p = ∀ {a b} → Hom[ a , b ] → hProp p

infix 5 _∈_
_∈_ : ∀ {p a b} → Hom[ a , b ] → ClassOfMorphism p → Type _
f ∈ 𝒞 = 𝒞 f .fst
