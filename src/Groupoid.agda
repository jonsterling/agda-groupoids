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

module Π = Groupoid.Exponential
module 𝟘 = Groupoid.Initial
module Op = Groupoid.Op
module Path = Groupoid.Path
module ∐ = Groupoid.Tensor
module 𝟙 = Groupoid.Terminal
module TFor = Groupoid.Transfor
