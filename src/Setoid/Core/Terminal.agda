{-# OPTIONS --without-K #-}

module Setoid.Core.Terminal where

open import Agda.Primitive
import Setoid.Core.Base as S
import Type as T

s : ∀ {d} → S.t d lzero lzero
S.obj s = T.𝟙.t
S.homᵗ s = T.Π.! T.𝟙.t
S.idnᵗ s = _
S.cmpᵗ s = _
S.invᵗ (s {S.Dir.≤}) = _
S.invᵗ (s {S.Dir.≈}) = _
