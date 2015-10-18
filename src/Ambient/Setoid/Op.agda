{-# OPTIONS --without-K #-}

module Ambient.Setoid.Op where

open import Agda.Primitive
import Ambient.Setoid.Base as S
open import Type as T

s : ∀ {d} ..{ℓᵒ ℓʰ}
  → S.𝔊₁ d ℓᵒ ℓʰ
  → S.𝔊₁ d ℓᵒ ℓʰ
S.cell₀ (s A) =
  Op₀ (S.cell₀ A)
S.cell₁ (s A) =
  S.cell₁ A ⇒₀.∘₀ ⟨ π¹₀ ,₀ π⁰₀ ⟩
S.idn (s A) =
  S.idn A
S.cmp (s A) =
  S.cmp A ⇒₀.∘₀ ⟨ π¹₀ ,₀ π⁰₀ ⟩
S.inv (s A) =
  S.inv A
