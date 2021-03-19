{-# OPTIONS --safe --without-K #-}
open import Categories.Category

module FactorizationSystem {o ℓ e} (𝒞 : Category o ℓ e) where

open import Lifting 𝒞
open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality

open Category 𝒞

private
  variable
    p : Level
    a b c d : Obj
    f : a ⇒ b
    g : c ⇒ d

-- should really be "a ⇒ b → Prop"
ClassOfMorphism : (p : Level) → Set _
ClassOfMorphism p = ∀ {a b} → a ⇒ b → Set p

Factorize : ClassOfMorphism p → ClassOfMorphism p → a ⇒ b → Set _
Factorize {a = a} {b = b} ℒ ℛ f = ∃[ c ] (Σ[ g ∈ a ⇒ c ] ℒ g × Σ[ h ∈ c ⇒ b ] ℛ h × f ≈ h ∘ g)

factors : ∀ {ℒ ℛ : ClassOfMorphism p} {a b} {f : a ⇒ b} → (F : Factorize ℒ ℛ f) → ∃[ c ] (a ⇒ c × c ⇒ b)
factors F = proj₁ F , proj₁ (proj₂ F) , proj₁ (proj₂ (proj₂ (proj₂ F)))

record FactorizationSystem (p : Level) : Set (o ⊔ ℓ ⊔ e ⊔ suc p) where
  field
    ℒ : ClassOfMorphism p
    ℛ : ClassOfMorphism p
    factorize : Factorize ℒ ℛ f
    lifting : ℒ f → ℛ g → f HasLiftingProperty g
    ℒ-byLifting : (∀ {c d} {g : c ⇒ d} → ℛ g → f HasLiftingProperty g) → ℒ f
    ℛ-byLifting : (∀ {a b} {f : a ⇒ b} → ℒ f → f HasLiftingProperty g) → ℛ g

record OrthogonalFactorizationSystem (p : Level) : Set (o ⊔ ℓ ⊔ e ⊔ suc p) where
  field
    factorization : FactorizationSystem p
  open FactorizationSystem factorization
  field
    uniqueness : ∀ {a b} {f : a ⇒ b} {F F' : Factorize ℒ ℛ f} → Σ[ e ∈ proj₁ F ≡ proj₁ F' ]
      factors {ℒ = ℒ} {ℛ = ℛ} F ≡ factors {ℒ = ℒ} {ℛ = ℛ} F'
    -- we cannot just say F ≡ F' since we lack the ability to truncate ℒ and ℛ without cubical
    -- and why is agda unable to infer ℒ and ℛ here?
