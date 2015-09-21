{-# OPTIONS --without-K #-}

module Type where

open import Type.Base public
import Type.Exponential
import Type.Initial
import Type.Op
import Type.Path
import Type.Tensor
import Type.Terminal
import Type.Transfor

module Π = Type.Exponential
module 𝟘 = Type.Initial
module Op = Type.Op
module Path = Type.Path
module ∐ = Type.Tensor
module 𝟙 = Type.Terminal
module TFor = Type.Transfor

open Type.Tensor public
  using (_,_)
