{-# OPTIONS --without-K #-}

module Ambient.Category.Base where

open import Agda.Primitive

module G where
  open import Groupoid public

module t where
  open G.t {G.Dir.≤} public
open t public

t : ∀ ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) → Set _
t = G.t G.Dir.≤
