{-# OPTIONS --cubical --safe --without-K #-}
module FactorizationSystem.Sets (o) where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Sets
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation
open import Function.Base
open import Prelude (SET o)
open import Lifting (SET o)
open import FactorizationSystem (SET o)
open import Lifting.Sets o
open Precategory (SET o)

AxiomOfChoice = ∀ {ℓ₁ ℓ₂} {A : hSet ℓ₁} (B : ⟨ A ⟩ → hSet ℓ₂) → (∀ x → ∥ ⟨ B x ⟩ ∥) → ∥(∀ x → ⟨ B x ⟩)∥

isEpic : ClassOfMorphism _
isEpic f = isSurjection f , isSurjectionIsProp

isMonic : ClassOfMorphism _
isMonic f = isEmbedding f , isEmbeddingIsProp

module _ {a b : hSet o} (f : ⟨ a ⟩ → ⟨ b ⟩) where
  Range : hSet o
  Range = (Σ[ x ∈ _ ] ∥ fiber f x ∥) , isSetΣ (str b) λ _ → isProp→isSet propTruncIsProp

  epicFactor : ⟨ a ⟩ → ⟨ Range ⟩
  epicFactor x = f x , ∣ x , refl ∣

  epicFactor-isEpic : isSurjection epicFactor
  epicFactor-isEpic (y , x') = map (λ(x , p) → x , (Σ≡Prop (λ _ → propTruncIsProp) p)) x'

  monicFactor : ⟨ Range ⟩ → ⟨ b ⟩
  monicFactor = fst

  monicFactor-isMonic : isEmbedding monicFactor
  monicFactor-isMonic = hasPropFibers→isEmbedding λ _ (_ , p) (_ , q) →
    Σ≡Prop (λ _ → str b _ _) (Σ≡Prop (λ _ → propTruncIsProp) (p ∙ sym q))

  epi-mono-factorize : Factorize {a = a} {b = b} (λ {a} {b} → isEpic {a} {b}) (λ {a} {b} → isMonic {a} {b}) f
  epi-mono-factorize =
    Range , epicFactor , epicFactor-isEpic , monicFactor , monicFactor-isMonic , refl

lifting-monic→epic : ∀ {a b : ob} {f : ⟨ a ⟩ → ⟨ b ⟩} →
  (∀ {c d : ob} {g : ⟨ c ⟩ → ⟨ d ⟩} → ⟨ isMonic {c} {d} g ⟩ → (_HasLiftingProperty_ {a} {b} {c} {d} f g)) →
  ⟨ isEpic {a} {b} f ⟩
lifting-monic→epic {a} {b} {f} H x = rec propTruncIsProp helper (H {c} {d} g-isMonic u v refl)
  where
  c = Range {a} {b} f
  d = b
  g = monicFactor {a} {b} f
  g-isMonic = monicFactor-isMonic {a} {b} f
  u = epicFactor {a} {b} f
  v = λ x → x

  helper : LiftingSolution {a} {b} {f} {c} {d} {g = g} {u = u} {v = v} refl → ∥ fiber f x ∥
  helper (γ , _ , right-comm) = map helper' (epicFactor-isEpic {a} {b} f (γ x))
    where
    helper' : fiber u (γ x) → fiber f x
    helper' (x' , p) = x' , cong fst p ∙ sym (funExt⁻ right-comm x)

epic-lifting→monic : ∀ {c d : ob} {g : ⟨ c ⟩ → ⟨ d ⟩} →
  (∀ {a b : ob} {f : ⟨ a ⟩ → ⟨ b ⟩} → ⟨ isEpic {a} {b} f ⟩ → (_HasLiftingProperty_ {a} {b} {c} {d} f g)) →
  ⟨ isMonic {c} {d} g ⟩
epic-lifting→monic {c} {d} {g} H = injEmbedding (str c) (str d)
  (rec (isProp→ (str c _ _)) (λ P → helper P _ _) (H {a} {b} f-isEpic u v refl))
  where
  a = c
  b = Range {c} {d} g
  f = epicFactor {c} {d} g
  f-isEpic = epicFactor-isEpic {c} {d} g
  u = λ x → x
  v = monicFactor {c} {d} g

  helper : LiftingSolution {a} {b} {f} {c} {d} {g = g} {u = u} {v = v} refl → ∀ x₁ x₂ → g x₁ ≡ g x₂ → x₁ ≡ x₂
  helper (γ , left-comm , _) x₁ x₂ p = funExt⁻ left-comm x₁ ∙ cong γ (Σ≡Prop (λ _ → propTruncIsProp) p)
    ∙ sym (funExt⁻ left-comm x₂)

EpicMonicFactorizationSystem : AxiomOfChoice → FactorizationSystem _
EpicMonicFactorizationSystem ac =
  record
    { ℒ = λ {a} {b} → isEpic {a} {b}
    ; ℛ = λ {a} {b} → isMonic {a} {b}
    -- I think we can safely conclude that agda is an idiot
    -- or maybe it's with the design of cubical agda library.  I don't know.
    -- perhaps isSet should be declared an instance field?
    -- but fundamentally, such h-level proofs should be automatically derived --- hence "HoTT-aware" proof assistants.
    ; factorize = λ {a} {b} → epi-mono-factorize {a} {b} _
    ; lifting = λ {a} {b} {f} {c} {d} f-epic → epi⁺-mono-lift {a} {b} {c} {d}
      (ac {A = b} (λ x → fiber f x , isSetΣ (str a) λ _ → isProp→isSet (str b _ _)) f-epic)
    ; ℒ-byLifting = λ {a} {b} → lifting-monic→epic {a} {b}
    ; ℛ-byLifting = λ {c} {d} → epic-lifting→monic {c} {d}
    }
