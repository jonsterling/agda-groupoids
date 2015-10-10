{-# OPTIONS --without-K #-}

module Category.Core.Base where

open import Agda.Primitive
open import Common
import Groupoid as G

module t where
  open G.t {Dir.≤} public
open t public

t : ∀ ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) → Set (lsuc (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ))
t = G.t Dir.≤
