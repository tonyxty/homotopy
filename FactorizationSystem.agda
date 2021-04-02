{-# OPTIONS --safe --cubical --without-K #-}
open import Cubical.Categories.Category.Base

module FactorizationSystem {ℓ ℓ'} (C : Precategory ℓ ℓ') where

open import Prelude C
open import Cubical.Foundations.Everything hiding (⋆)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.HITs.PropositionalTruncation
open import Lifting C

open Precategory C

private
  variable
    p : Level
    a b c d : ob
    f : Hom[ a , b ]
    g : Hom[ c , d ]

Factorize : ClassOfMorphism p → ClassOfMorphism p → Hom[ a , b ] → Type _
Factorize {a = a} {b = b} ℒ ℛ f =
  Σ[ c ∈ ob ] (Σ[ g ∈ Hom[ a , c ] ] (g ∈ ℒ) × (Σ[ h ∈ Hom[ c , b ] ] (h ∈ ℛ) × (f ≡ g ⋆ h)))

record FactorizationSystem (p : Level) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc p)) where
  field
    ℒ : ClassOfMorphism p
    ℛ : ClassOfMorphism p
    factorize : Factorize ℒ ℛ f
    lifting : f ∈ ℒ → g ∈ ℛ → f HasLiftingProperty g
    ℒ-byLifting : (∀ {c d} {g : Hom[ c , d ]} → g ∈ ℛ → f HasLiftingProperty g) → f ∈ ℒ
    ℛ-byLifting : (∀ {a b} {f : Hom[ a , b ]} → f ∈ ℒ → f HasLiftingProperty g) → g ∈ ℛ

record OrthogonalFactorizationSystem (p : Level) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc p)) where
  field
    factorization : FactorizationSystem p
  open FactorizationSystem factorization
  field
    uniqueness : isProp (Factorize ℒ ℛ f)
