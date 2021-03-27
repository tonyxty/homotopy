{-# OPTIONS --safe --cubical --without-K #-}
open import Cubical.Categories.Category.Base

module Lifting.Properties {ℓ ℓ'} (C : Precategory ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Categories.Morphism
open import Lifting C

open Precategory C

private
  variable
    a b c d : ob
    f : Hom[ a , b ]
    g : Hom[ c , d ]

isIso→liftˡ : isIso {C = C} f → f HasLiftingProperty g
-- why do we need the {C = C} here?
isIso→liftˡ {f = f} {g = g} iso {u = u} {v = v} P =
  ∣ inv ⋆ u , sym (sym (⋆Assoc f inv u) ∙ cong (_⋆ u) ret ∙ ⋆IdL u) ,
    sym (⋆Assoc inv u g ∙ cong (inv ⋆_) (sym P) ∙ sym (⋆Assoc inv f v) ∙ cong (_⋆ v) sec ∙ ⋆IdL v) ∣
  where open isIso iso

isIso→liftʳ : isIso {C = C} g → f HasLiftingProperty g
isIso→liftʳ {g = g} {f = f} iso {u = u} {v = v} P =
  ∣ v ⋆ inv , sym (sym (⋆Assoc f v inv) ∙ cong (_⋆ inv) P ∙ ⋆Assoc u g inv ∙ cong (u ⋆_) ret ∙ ⋆IdR u) ,
    sym (⋆Assoc v inv g ∙ cong (v ⋆_) sec ∙ ⋆IdR v) ∣
  where open isIso iso
