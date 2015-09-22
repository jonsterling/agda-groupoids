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

module Π where
  open import Type.Exponential public
  open import Type.Exponential.Boot public
module 𝟘 = Type.Initial
module Op = Type.Op
module Path = Type.Path
module ∐ where
  open import Type.Tensor public
  open import Type.Tensor.Boot public
module 𝟙 = Type.Terminal
module TFor = Type.Transfor

open Type.Tensor public
  using (_,_)
