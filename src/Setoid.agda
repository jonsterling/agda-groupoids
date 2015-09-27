{-# OPTIONS --without-K #-}

module Setoid where

open import Agda.Primitive
open import Setoid.Base public
import Setoid.Discrete
import Setoid.Exponential
import Setoid.Homotopy
import Setoid.Initial
import Setoid.Op
import Setoid.Tensor
import Setoid.Terminal

module ≡ where
  open import Setoid.Discrete public
module Π where
  open import Setoid.Exponential public
  open import Setoid.Exponential.Boot public
module TFor = Setoid.Homotopy
module 𝟘 = Setoid.Initial
module Op = Setoid.Op
module ∐ where
  open import Setoid.Tensor public
  open import Setoid.Tensor.Boot public
module 𝟙 = Setoid.Terminal
