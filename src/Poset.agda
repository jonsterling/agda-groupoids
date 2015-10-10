{-# OPTIONS --without-K #-}

module Poset where

open import Agda.Primitive
import Setoid.Core.Base
open import Common public

open import Poset.Core.Base public
import Setoid.Closed
import Setoid.Core.Discrete
import Setoid.Core.Hom
import Setoid.Core.Homotopy
import Setoid.Core.Initial
import Setoid.Core.Op
import Setoid.Core.Tensor
import Setoid.Core.Terminal
import Setoid.Monoidal

module Discrete where
  open import Setoid.Core.Discrete public
module Π where
  open import Setoid.Core.Hom public
  open import Setoid.Core.Hom.Boot public
module TF where
  open import Setoid.Core.Homotopy public
module 𝟘 where
  open import Setoid.Core.Initial public
module Op where
  open import Setoid.Core.Op public
module ∐ where
  open import Setoid.Core.Tensor public
  open import Setoid.Core.Tensor.Boot public
module 𝟙 where
  open import Setoid.Core.Terminal public
