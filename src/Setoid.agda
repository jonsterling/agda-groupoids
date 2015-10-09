{-# OPTIONS --without-K #-}

module Setoid where

open import Agda.Primitive
open import Setoid.Core.Base public
import Setoid.Core.Discrete
import Setoid.Core.Exponential
import Setoid.Core.Homotopy
import Setoid.Core.Initial
import Setoid.Core.Op
import Setoid.Core.Tensor
import Setoid.Core.Terminal

module ≡ where
  open import Setoid.Core.Discrete public
module Π where
  open import Setoid.Core.Exponential public
  open import Setoid.Core.Exponential.Boot public
module TFor = Setoid.Core.Homotopy
module 𝟘 = Setoid.Core.Initial
module Op = Setoid.Core.Op
module ∐ where
  open import Setoid.Core.Tensor public
  open import Setoid.Core.Tensor.Boot public
module 𝟙 = Setoid.Core.Terminal
