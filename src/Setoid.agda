{-# OPTIONS --without-K #-}

module Setoid where

open import Setoid.Base public
import Setoid.Exponential
import Setoid.Initial
import Setoid.Op
import Setoid.Path
import Setoid.Tensor
import Setoid.Terminal
import Setoid.Transfor

module Π where
  open import Setoid.Exponential public
  open import Setoid.Exponential.Boot public
module 𝟘 = Setoid.Initial
module Op = Setoid.Op
module Path = Setoid.Path
module ∐ where
  open import Setoid.Tensor public
  open import Setoid.Tensor.Boot public
module 𝟙 = Setoid.Terminal
module TFor = Setoid.Transfor
