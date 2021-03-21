{-# OPTIONS --cubical --safe --without-K #-}
module FactorizationSystem.Sets (o) where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Sets
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation
open import FactorizationSystem (SET o)
open import Lifting.Sets o

Epic : ClassOfMorphism _
Epic f = isSurjection f , isSurjectionIsProp

Monic : ClassOfMorphism _
Monic f = isEmbedding f , isEmbeddingIsProp

Range : ∀ {a b : hSet o} (f : typ a → typ b) → hSet o
Range {a = a} {b = b} f = (Σ[ x ∈ _ ] ∥ fiber f x ∥) , isSetΣ (str b) λ _ → isProp→isSet propTruncIsProp

epi-mono-factorize : ∀ {a b : hSet o} (f : typ a → typ b) →
  Factorize {a = a} {b = b} (λ {a} {b} → Epic {a} {b}) (λ {a} {b} → Monic {a} {b}) f  -- wtf????
epi-mono-factorize {a = a} {b = b} f = ran , fˡ , fˡ-isSurjection , fʳ , fʳ-isEmbedding , refl
  where
  ran : hSet o
  ran = Range {a} {b} f

  fˡ : typ a → typ ran
  fˡ x = f x , ∣ x , refl ∣

  fˡ-isSurjection : isSurjection fˡ
  fˡ-isSurjection (y , x') = map (λ x → (fst x) , (Σ≡Prop (λ _ → propTruncIsProp) (snd x))) x'

  fʳ : typ ran → typ b
  fʳ = fst

  fʳ-isEmbedding : isEmbedding fʳ
  fʳ-isEmbedding = hasPropFibers→isEmbedding λ _ (_ , p) (_ , q) →
    Σ≡Prop (λ _ → str b _ _) (Σ≡Prop (λ _ → propTruncIsProp) (p ∙ sym q))

EpicMonicFactorizationSystem : AxiomOfChoice → FactorizationSystem _
EpicMonicFactorizationSystem ac =
  record
    { ℒ = λ {a} {b} → Epic {a} {b}
    ; ℛ = λ {a} {b} → Monic {a} {b}
    -- I think we can safely conclude that agda is an idiot
    ; factorize = λ {a} {b} → epi-mono-factorize {a} {b} _
    ; lifting = λ {a} {b} {_} {c} {d} → epi-mono-lift {a} {b} {c} {d} ac
    ; ℒ-byLifting = {!!}
    ; ℛ-byLifting = {!!}
    }
