{-# OPTIONS --without-K #-}

module Type where

open import Agda.Primitive
open import Type.Core.Base public
import Type.Closed
import Type.Core.Discrete
import Type.Core.Hom
import Type.Core.Homotopy
import Type.Core.Initial
import Type.Core.Op
import Type.Core.Tensor
import Type.Core.Terminal
import Type.Monoidal

module ≡ where
  open import Type.Core.Discrete public
    renaming (t to _t_)
module Π where
  open import Type.Core.Hom public
  open import Type.Core.Hom.Boot public
module TFor = Type.Core.Homotopy
module 𝟘 = Type.Core.Initial
module Op = Type.Core.Op
module ∐ where
  open import Type.Core.Tensor public
  open import Type.Core.Tensor.Boot public
module 𝟙 = Type.Core.Terminal

open Type.Core.Tensor public
  using (_,_)
