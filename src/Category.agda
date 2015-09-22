{-# OPTIONS --without-K #-}

module Category where

open import Agda.Primitive

import Groupoid.Base
open import Common public

t : ∀ ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) → Set (lsuc (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ))
t = Groupoid.Base.t Dir.≤

import Groupoid.Discrete
import Groupoid.Exponential
import Groupoid.Initial
import Groupoid.Op
import Groupoid.Tensor
import Groupoid.Terminal
import Groupoid.Transfor

module Discrete = Groupoid.Discrete
module Π where
  open import Groupoid.Exponential public
  open import Groupoid.Exponential.Boot public
module 𝟘 = Groupoid.Initial
module Op = Groupoid.Op
module ∐ where
  open import Groupoid.Tensor public
  open import Groupoid.Tensor.Boot public
module 𝟙 = Groupoid.Terminal
module TFor = Groupoid.Transfor
