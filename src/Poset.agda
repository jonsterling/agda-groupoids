{-# OPTIONS --without-K #-}

module Poset where

open import Agda.Primitive

import Setoid.Base
open import Common public

t : ∀ ..(ℓᵒ ℓʰ : _) → Set (lsuc (ℓᵒ ⊔ ℓʰ))
t = Setoid.Base.t Dir.≤

import Setoid.Discrete
import Setoid.Exponential
import Setoid.Initial
import Setoid.Op
import Setoid.Tensor
import Setoid.Terminal
import Setoid.Transfor

module Discrete = Setoid.Discrete
module Π where
  open import Setoid.Exponential public
  open import Setoid.Exponential.Boot public
module 𝟘 = Setoid.Initial
module Op = Setoid.Op
module ∐ where
  open import Setoid.Tensor public
  open import Setoid.Tensor.Boot public
module 𝟙 = Setoid.Terminal
module TFor = Setoid.Transfor
