{-# OPTIONS --without-K #-}

module Type where

open import Agda.Primitive
open import Type.Base public
import Type.Discrete
import Type.Exponential
import Type.Initial
import Type.Op
import Type.Tensor
import Type.Terminal
import Type.Transfor

module Discrete = Type.Discrete
module Π where
  open import Type.Exponential public
  open import Type.Exponential.Boot public
module 𝟘 = Type.Initial
module Op = Type.Op
module ∐ where
  open import Type.Tensor public
  open import Type.Tensor.Boot public
module 𝟙 = Type.Terminal
module TFor = Type.Transfor

open Type.Tensor public
  using (_,_)
