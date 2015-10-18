{-# OPTIONS --without-K #-}

module Ambient.Setoid.Initial where

open import Agda.Primitive
import Ambient.Setoid.Base as S
import Ambient.Setoid.Map as Map
open import Type as T

s : ∀ {d} ..{ℓᵒ ℓʰ}
  → S.𝔊₁ d ℓᵒ ℓʰ
S.cell₀ s = 𝟘₀
S.cell₁ s = λ {((), _)}
S.idn s = λ {}
S.cmp s = λ {}
S.inv s = λ {}

¡ : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
  → s {ℓᵒ = ℓ₀ᵒ}{ℓ₀ʰ} Map.⇒₀ᵗ A
Map._$₀_ ¡ = λ ()
Map._$₁_ ¡ = λ {}

¬_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ)
  → Set _
¬_ {ℓ₀ᵒ = ℓ₀ᵒ}{ℓ₀ʰ} A = A Map.⇒₀ᵗ s {ℓᵒ = ℓ₀ᵒ}{ℓ₀ʰ}
