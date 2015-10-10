{-# OPTIONS --without-K #-}

module Poset.Core.Base where

open import Agda.Primitive
open import Common

module S where
  open import Setoid public

module t where
  open S.t {Dir.≤} public
open t public

t : ∀ ..(ℓᵒ ℓʰ : _) → Set _
t = S.t Dir.≤
