{-# OPTIONS --without-K #-}

module Type.Core.Base where

open import Agda.Primitive

t : ∀ ..ℓᵒ → Set (lsuc ℓᵒ)
t ℓᵒ = Set ℓᵒ
