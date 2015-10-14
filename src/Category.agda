{-# OPTIONS --without-K #-}

module Category where

open import Agda.Primitive
import Ambient.Groupoid.Base

open import Ambient.Category.Base public
import Ambient.Groupoid.Discrete
import Ambient.Groupoid.Map
import Ambient.Groupoid.Initial
import Ambient.Groupoid.Op
import Ambient.Groupoid.Tensor
import Ambient.Groupoid.Terminal
import Groupoid.Closed
import Groupoid.Monoidal

module ≡ where
  open import Ambient.Groupoid.Discrete public
module 𝟘 where
  open import Ambient.Groupoid.Initial public
module 𝟙 where
  open import Ambient.Groupoid.Terminal public
module Op where
  open import Ambient.Groupoid.Op public
module Map where
  open import Ambient.Groupoid.Map public
  open import Ambient.Groupoid.Map.Boot public
module Ten where
  open import Ambient.Groupoid.Tensor public
  open import Ambient.Groupoid.Tensor.Boot public
