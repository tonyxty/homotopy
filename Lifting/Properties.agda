{-# OPTIONS --safe --cubical --without-K #-}
open import Cubical.Categories.Category.Base

module Lifting.Properties {ℓ ℓ'} (C : Precategory ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Morphism
open import Lifting C

open Precategory C

private
  variable
    a b c d : ob
    f f₁ f₂ : Hom[ a , b ]
    g g₁ g₂ : Hom[ c , d ]

isIso→liftˡ : isIso {C = C} f → f HasLiftingProperty g
-- why do we need the {C = C} here?
isIso→liftˡ {f = f} {g = g} iso u v P =
  ∣ inv ⋆ u , sym (sym (⋆Assoc f inv u) ∙ cong (_⋆ u) ret ∙ ⋆IdL u) ,
    sym (⋆Assoc inv u g ∙ cong (inv ⋆_) (sym P) ∙ sym (⋆Assoc inv f v) ∙ cong (_⋆ v) sec ∙ ⋆IdL v) ∣
  where open isIso iso

isIso→liftʳ : isIso {C = C} g → f HasLiftingProperty g
isIso→liftʳ {g = g} {f = f} iso u v P =
  ∣ v ⋆ inv , sym (sym (⋆Assoc f v inv) ∙ cong (_⋆ inv) P ∙ ⋆Assoc u g inv ∙ cong (u ⋆_) ret ∙ ⋆IdR u) ,
    sym (⋆Assoc v inv g ∙ cong (v ⋆_) sec ∙ ⋆IdR v) ∣
  where open isIso iso

⋆-liftˡ : f₁ HasLiftingProperty g → f₂ HasLiftingProperty g → (f₁ ⋆ f₂) HasLiftingProperty g
⋆-liftˡ {f₁ = f₁} {f₂ = f₂} LP₁ LP₂ u v P = rec propTruncIsProp (λ(h' , left-comm' , right-comm') → map
  (λ(h , left-comm , right-comm) → h , left-comm' ∙ cong (f₁ ⋆_) left-comm ∙ sym (⋆Assoc f₁ f₂ h) , right-comm)
  (LP₂ h' v right-comm')) (LP₁ u (f₂ ⋆ v) (sym (⋆Assoc f₁ f₂ v) ∙ P))

⋆-liftʳ : f HasLiftingProperty g₁ → f HasLiftingProperty g₂ → f HasLiftingProperty (g₁ ⋆ g₂)
⋆-liftʳ {g₁ = g₁} {g₂ = g₂} LP₁ LP₂ u v P = rec propTruncIsProp (λ(h' , left-comm' , right-comm') → map
  (λ(h , left-comm , right-comm) → h , left-comm , right-comm' ∙ cong (_⋆ g₂) right-comm ∙ ⋆Assoc h g₁ g₂)
  (LP₁ u h' (sym left-comm'))) (LP₂ (u ⋆ g₁) v (P ∙ sym (⋆Assoc u g₁ g₂)))
