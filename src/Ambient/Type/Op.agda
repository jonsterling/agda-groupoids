{-# OPTIONS --without-K #-}

module Ambient.Type.Op where

open import Ambient.Type.Base

Op₀
  : ∀ ..{ℓᵒ}
  → (A : 𝔊₀ ℓᵒ)
  → 𝔊₀ ℓᵒ
Op₀ A = A
