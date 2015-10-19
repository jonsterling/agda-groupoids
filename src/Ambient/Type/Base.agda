{-# OPTIONS --without-K #-}

module Ambient.Type.Base where

open import Agda.Primitive

t : ∀ ..ℓᵒ → Set (lsuc ℓᵒ)
t ℓᵒ = Set ℓᵒ
