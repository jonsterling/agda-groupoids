{-# OPTIONS --without-K #-}

module Ambient.Type.Product.Boot where

open import Agda.Primitive

infixr 0 _,_
infixr 1 _×₀_

record _×₀_ ..{ℓ₀ ℓ₁}
  (A : Set ℓ₀)
  (B : Set ℓ₁)
    : Set (ℓ₀ ⊔ ℓ₁) where
  constructor _,_
  field
    π⁰₀ : A
    π¹₀ : B
open _×₀_ public
