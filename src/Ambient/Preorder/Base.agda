{-# OPTIONS --without-K #-}

module Ambient.Preorder.Base where

open import Agda.Primitive
open import Common

module S where
  open import Setoid public

module t where
  open S.𝔊₁ {Dir.≤} public
open t public

t : ∀ ..(ℓᵒ ℓʰ : _) → Set _
t = S.𝔊₁ Dir.≤
