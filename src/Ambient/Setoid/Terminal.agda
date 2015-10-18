{-# OPTIONS --without-K #-}

module Ambient.Setoid.Terminal where

open import Agda.Primitive
import Ambient.Setoid.Base as S
open import Type as T

s : ∀ {d} ..{ℓᵒ ℓʰ} → S.𝔊₁ d ℓᵒ ℓʰ
S.cell₀ s = 𝟙₀
S.cell₁ s = ⇒₀.elm₀ 𝟙₀
S.idn s = _
S.cmp s = _
S.inv (s {S.Dir.≤}) = _
S.inv (s {S.Dir.≈}) = _

s⁰ : ∀ {d} → S.𝔊₁ d lzero lzero
s⁰ = s
