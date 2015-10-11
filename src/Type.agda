{-# OPTIONS --without-K #-}

module Type where

open import Agda.Primitive
open import Type.Core.Base public
import Type.Core.Discrete
import Type.Core.Hom
import Type.Core.Homotopy
import Type.Core.Initial
import Type.Core.Op
import Type.Core.Tensor
import Type.Core.Terminal

module ≡ where
  open import Type.Core.Discrete public
    renaming (t to _t_)
module Π where
  open import Type.Core.Hom public
  open import Type.Core.Hom.Boot public
module TF where
  open import Type.Core.Homotopy public
module 𝟘 where
  open import Type.Core.Initial public
module Op where
  open import Type.Core.Op public
module ∐ where
  open import Type.Core.Tensor public
  open import Type.Core.Tensor.Boot public
module 𝟙 where
  open import Type.Core.Terminal public

open Type.Core.Tensor public
  using (_,_)
