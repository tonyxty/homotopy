{-# OPTIONS --safe --cubical --without-K #-}
module Lifting.Sets (ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Base
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Sets
open import Cubical.HITs.PropositionalTruncation
open import Lifting (SET ℓ)

open Precategory (SET ℓ)

surj-inj-lift : ∀ {a b c d : ob} {f : Hom[ a , b ]} {g : Hom[ c , d ]} →
  ∃[ h ∈ _ ] (section f h) → isEmbedding g → _HasLiftingProperty_ {a = a} {b = b} {c = c} {d = d} f g
surj-inj-lift {a@(A , _)} {b@(B , _)} {c@(C , _)} {d@(D , _)} {f} {g} f-surj g-emb {u = u} {v = v} P =
  map (helper g-inj) f-surj'
  where
  f-surj' : ∥ (∀ x → fiber f x) ∥
  f-surj' = map (λ(h , s) x → h x , s x) f-surj

  g-inj : ∀ {x x'} → g x ≡ g x' → x ≡ x'
  g-inj {x} {x'} p = cong fst (isEmbedding→hasPropFibers g-emb (g x') (x , p) (x' , refl))

  helper : (∀ {x x'} → g x ≡ g x' → x ≡ x') → (∀ x → fiber f x) → LiftingSolution {a} {b} {f} {c} {d} {g} {u} {v} P
  helper t s = (λ x → u (fst (s x))) , funExt (λ x → t (sym (funExt⁻ P x) ∙ right-comm (f x))) , funExt right-comm
    where
    right-comm : ∀ x → v x ≡ g (u (fst (s x)))
    right-comm x = sym (cong v (snd (s x))) ∙ funExt⁻ P (fst (s x))
