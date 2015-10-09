{-# OPTIONS --without-K #-}

module Groupoid where

open import Agda.Primitive
open import Groupoid.Core.Base public
import Groupoid.Core.Discrete
import Groupoid.Core.Exponential
import Groupoid.Core.Homotopy
import Groupoid.Core.Initial
import Groupoid.Core.Op
import Groupoid.Core.Tensor
import Groupoid.Core.Terminal

module ≡ where
  open import Groupoid.Core.Discrete public
module Π where
  open import Groupoid.Core.Exponential public
  open import Groupoid.Core.Exponential.Boot public
module TFor = Groupoid.Core.Homotopy
module 𝟘 = Groupoid.Core.Initial
module Op = Groupoid.Core.Op
module ∐ where
  open import Groupoid.Core.Tensor public
  open import Groupoid.Core.Tensor.Boot public
module 𝟙 = Groupoid.Core.Terminal
