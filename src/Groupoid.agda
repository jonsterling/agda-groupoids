{-# OPTIONS --without-K #-}

module Groupoid where

open import Agda.Primitive
open import Groupoid.Base public
import Groupoid.Discrete
import Groupoid.Exponential
import Groupoid.Homotopy
import Groupoid.Initial
import Groupoid.Op
import Groupoid.Tensor
import Groupoid.Terminal

module ≡ where
  open import Groupoid.Discrete public
module Π where
  open import Groupoid.Exponential public
  open import Groupoid.Exponential.Boot public
module TFor = Groupoid.Homotopy
module 𝟘 = Groupoid.Initial
module Op = Groupoid.Op
module ∐ where
  open import Groupoid.Tensor public
  open import Groupoid.Tensor.Boot public
module 𝟙 = Groupoid.Terminal
