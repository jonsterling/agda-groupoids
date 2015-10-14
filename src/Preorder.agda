{-# OPTIONS --without-K #-}

module Preorder where

open import Agda.Primitive
import Ambient.Setoid.Base
open import Common public

open import Ambient.Preorder.Base public
import Ambient.Setoid.Discrete
import Ambient.Setoid.Initial
import Ambient.Setoid.Map
import Ambient.Setoid.Op
import Ambient.Setoid.Tensor
import Ambient.Setoid.Terminal

module ≡ where
  open import Ambient.Setoid.Discrete public
module 𝟘 where
  open import Ambient.Setoid.Initial public
module 𝟙 where
  open import Ambient.Setoid.Terminal public
module Op where
  open import Ambient.Setoid.Op public
module Map where
  open import Ambient.Setoid.Map public
  open import Ambient.Setoid.Map.Boot public
module Ten where
  open import Ambient.Setoid.Tensor public
  open import Ambient.Setoid.Tensor.Boot public
