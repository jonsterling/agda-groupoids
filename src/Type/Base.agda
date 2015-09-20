{-# OPTIONS --sized-types --without-K #-}

module Type.Base where

open import Agda.Primitive

t : ∀ ..ℓᵒ → Set (lsuc ℓᵒ)
t ℓᵒ = Set ℓᵒ
