{-# OPTIONS --safe --cubical --without-K #-}
open import Cubical.Categories.Category.Base

module WeakEquivalence {ℓ ℓ'} (C : Precategory ℓ ℓ') where

open import Cubical.Foundations.Everything hiding (isIso; ⋆)
open import Cubical.Categories.Morphism
open import FactorizationSystem C using (ClassOfMorphism)

open Precategory C

record WeakEquivalence (p : Level) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc p)) where
  field
    𝒲 : ClassOfMorphism p
    byIso : ∀ {a b : ob} {f : Hom[ a , b ]} → isIso {C = C} f → typ (𝒲 f)
    2-3-⋆ : ∀ {a b c : ob} {f : Hom[ a , b ]} {g : Hom[ b , c ]} → typ (𝒲 f) → typ (𝒲 g) → typ (𝒲 (f ⋆ g))
    2-3-left : ∀ {a b c : ob} {f : Hom[ a , b ]} {g : Hom[ b , c ]} → typ (𝒲 (f ⋆ g)) → typ (𝒲 g) → typ (𝒲 f)
    2-3-right : ∀ {a b c : ob} {f : Hom[ a , b ]} {g : Hom[ b , c ]} → typ (𝒲 (f ⋆ g)) → typ (𝒲 f) → typ (𝒲 g)
