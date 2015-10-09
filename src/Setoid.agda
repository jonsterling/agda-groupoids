{-# OPTIONS --without-K #-}

module Setoid where

open import Agda.Primitive
open import Setoid.Core.Base public
import Setoid.Closed
import Setoid.Core.Discrete
import Setoid.Core.Hom
import Setoid.Core.Homotopy
import Setoid.Core.Initial
import Setoid.Core.Op
import Setoid.Core.Tensor
import Setoid.Core.Terminal
import Setoid.Monoidal

module ≡ where
  open import Setoid.Core.Discrete public
module Π where
  open import Setoid.Core.Hom public
  open import Setoid.Core.Hom.Boot public
module TFor = Setoid.Core.Homotopy
module 𝟘 = Setoid.Core.Initial
module Op = Setoid.Core.Op
module ∐ where
  open import Setoid.Core.Tensor public
  open import Setoid.Core.Tensor.Boot public
module 𝟙 = Setoid.Core.Terminal
