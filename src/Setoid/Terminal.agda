{-# OPTIONS --without-K #-}

module Setoid.Terminal where

open import Agda.Primitive
import Setoid.Base as S
import Type as T

s : ∀ {d} → S.t d lzero lzero
S.obj s = T.𝟙.t
S.homᵗ s = T.Π.! T.𝟙.t
S.idnᵗᵐ s = _
S.cmpᵗᵐ s = _
S.invᵗᵐ (s {S.Dir.≤}) = _
S.invᵗᵐ (s {S.Dir.≈}) = _
