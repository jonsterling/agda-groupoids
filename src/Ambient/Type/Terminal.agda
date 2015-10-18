{-# OPTIONS --without-K #-}

module Ambient.Type.Terminal where

open import Agda.Primitive

record 𝟙₀ ..{ℓ} : Set ℓ where
  constructor *
