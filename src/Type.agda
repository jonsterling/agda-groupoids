{-# OPTIONS --sized-types --without-K #-}

module Type where

open import Type.Base public
import Type.Exponential
import Type.Homotopy
import Type.Initial
import Type.Op
import Type.Path
import Type.Tensor
import Type.Terminal

module Π = Type.Exponential
module Homo = Type.Homotopy
module 𝟘 = Type.Initial
module Op = Type.Op
module Path = Type.Path
module ∐ = Type.Tensor
module 𝟙 = Type.Terminal

open Type.Tensor public
  using (_,_)
