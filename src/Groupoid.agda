{-# OPTIONS --without-K #-}

module Groupoid where

open import Groupoid.Base public
import Groupoid.Exponential
import Groupoid.Initial
import Groupoid.Op
import Groupoid.Path
import Groupoid.Tensor
import Groupoid.Terminal
import Groupoid.Transfor

module Π where
  open import Groupoid.Exponential public
  open import Groupoid.Exponential.Boot public
module 𝟘 = Groupoid.Initial
module Op = Groupoid.Op
module Path = Groupoid.Path
module ∐ where
  open import Groupoid.Tensor public
  open import Groupoid.Tensor.Boot public
module 𝟙 = Groupoid.Terminal
module TFor = Groupoid.Transfor
