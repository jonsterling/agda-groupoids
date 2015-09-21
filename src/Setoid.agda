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

module Π = Setoid.Exponential
module 𝟘 = Setoid.Initial
module Op = Setoid.Op
module Path = Setoid.Path
module ∐ = Setoid.Tensor
module 𝟙 = Setoid.Terminal
module TFor = Setoid.Transfor
