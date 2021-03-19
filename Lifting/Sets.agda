{-# OPTIONS --safe --without-K #-}
module Lifting.Sets (o) where

open import Categories.Category.Instance.Sets
open import Lifting (Sets o)
open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality

private
  variable
    a b c d : Set o
    f : a → b
    g : c → d

epi-mono-lift : (Surjective {A = a} _≡_ _≡_ f) → (Injective _≡_ _≡_ g) → f HasLiftingProperty g
-- why is agda unable to infer {A = a} ???
epi-mono-lift f-surj g-inj {u = u} {v = v} P = (λ x → u (proj₁ (f-surj x))) , g-inj (trans (sym P) helper) , helper
  where
  helper = λ {x} → trans (sym (cong v (proj₂ (f-surj x)))) P
