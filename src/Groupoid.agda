{-# OPTIONS --without-K #-}

module Groupoid where

open import Agda.Primitive
open import Groupoid.Core.Base public
import Groupoid.Closed
import Groupoid.Core.Discrete
import Groupoid.Core.Hom
import Groupoid.Core.Homotopy
import Groupoid.Core.Initial
import Groupoid.Core.Op
import Groupoid.Core.Tensor
import Groupoid.Core.Terminal
import Groupoid.Monoidal

module ≡ where
  open import Groupoid.Core.Discrete public
module Π where
  open import Groupoid.Core.Hom public
  open import Groupoid.Core.Hom.Boot public
module TF where
  open import Groupoid.Core.Homotopy public
module 𝟘 where
  open import Groupoid.Core.Initial public
module Op where
  open import Groupoid.Core.Op public
module ∐ where
  open import Groupoid.Core.Tensor public
  open import Groupoid.Core.Tensor.Boot public
module 𝟙 where
  open import Groupoid.Core.Terminal public
