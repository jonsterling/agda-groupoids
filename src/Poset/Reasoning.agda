{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Common
import Poset.Core.Base as P
open import Type as T
  using (_,_)

module Poset.Reasoning ..{ℓᵒ ℓʰ} (A : P.t ℓᵒ ℓʰ) where
  infix  4 _⊢≤_
  infix  3 _∎
  infixr 2 _≤⟨_⟩_
  infix  1 proof_

  data _⊢≤_ (a b : P.obj A) : Set ℓʰ where
    [_] : (a≤b : P.homᵗ A (a , b)) → a ⊢≤ b

  proof_ : ∀ {a b} → a ⊢≤ b → P.homᵗ A (a , b)
  proof [ a≤b ] = a≤b

  _∎ : ∀ a → a ⊢≤ a
  _∎ _ = [ P.idnᵗᵐ A T.𝟙.* ]

  _≤⟨_⟩_ : ∀ a {b c} → P.homᵗ A (a , b) → b ⊢≤ c → a ⊢≤ c
  _ ≤⟨ a≤b ⟩ [ b≤c ] = [ P.cmpᵗᵐ A (b≤c , a≤b) ]
