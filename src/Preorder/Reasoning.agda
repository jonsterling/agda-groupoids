{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Common
import Ambient.Preorder.Base as P
open import Type as T

module Preorder.Reasoning ..{ℓᵒ ℓʰ} (A : P.t ℓᵒ ℓʰ) where
  infix  4 _⊢≤_
  infix  3 _∎
  infixr 2 _≤⟨_⟩_
  infix  1 proof_

  data _⊢≤_ (a b : P.cell₀ A) : Set ℓʰ where
    [_] : (a≤b : P.cell₁ A (a , b)) → a ⊢≤ b

  proof_ : ∀ {a b} → a ⊢≤ b → P.cell₁ A (a , b)
  proof [ a≤b ] = a≤b

  _∎ : ∀ a → a ⊢≤ a
  _∎ _ = [ P.idn A * ]

  _≤⟨_⟩_ : ∀ a {b c} → P.cell₁ A (a , b) → b ⊢≤ c → a ⊢≤ c
  _ ≤⟨ a≤b ⟩ [ b≤c ] = [ P.cmp A (b≤c , a≤b) ]
