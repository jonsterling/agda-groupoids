{-# OPTIONS --without-K #-}

module Ambient.Type.Base where

open import Agda.Primitive

𝔊₀ : ∀ ..ℓᵒ → Set (lsuc ℓᵒ)
𝔊₀ ℓᵒ = Set ℓᵒ
