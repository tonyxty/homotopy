{-# OPTIONS --safe --cubical --without-K #-}
open import Cubical.Categories.Category.Base

module WeakEquivalence {ℓ ℓ'} (C : Precategory ℓ ℓ') where

open import Prelude C
open import Cubical.Foundations.Everything hiding (isIso; ⋆)
open import Cubical.Categories.Morphism

open Precategory C

record WeakEquivalence (p : Level) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc p)) where
  field
    𝒲 : ClassOfMorphism p
    byIso : ∀ {a b : ob} {f : Hom[ a , b ]} → isIso {C = C} f → f ∈ 𝒲
    2-3-⋆ : ∀ {a b c : ob} {f : Hom[ a , b ]} {g : Hom[ b , c ]} → f ∈ 𝒲 → g ∈ 𝒲 → f ⋆ g ∈ 𝒲
    2-3-left : ∀ {a b c : ob} {f : Hom[ a , b ]} {g : Hom[ b , c ]} → f ⋆ g ∈ 𝒲 → g ∈ 𝒲 → f ∈ 𝒲
    2-3-right : ∀ {a b c : ob} {f : Hom[ a , b ]} {g : Hom[ b , c ]} → f ⋆ g ∈ 𝒲 → f ∈ 𝒲 → g ∈ 𝒲
