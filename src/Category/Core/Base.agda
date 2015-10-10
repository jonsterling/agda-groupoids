{-# OPTIONS --without-K #-}

module Category.Core.Base where

open import Agda.Primitive
open import Common

module G where
  open import Groupoid public

module t where
  open G.t {Dir.≤} public
open t public

t : ∀ ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) → Set _
t = G.t Dir.≤
