{-# OPTIONS --without-K #-}

module Ambient.Setoid.Initial where

open import Agda.Primitive
import Ambient.Setoid.Base as S
import Ambient.Setoid.Map as Map
open import Type as T
  using (_,_)

s : ∀ {d} ..{ℓᵒ ℓʰ}
  → S.t d ℓᵒ ℓʰ
S.obj s = T.𝟘.t
S.homᵗ s = λ {((), _)}
S.idnᵗ s = λ {}
S.cmpᵗ s = λ {}
S.invᵗ s = λ {}

¡ : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → s {ℓᵒ = ℓ₀ᵒ}{ℓ₀ʰ} Map.⇒₀ᵗ A
Map._$₀_ ¡ = λ ()
Map._$₁_ ¡ = λ {}

¬_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t d ℓ₁ᵒ ℓ₁ʰ)
  → Set _
¬_ {ℓ₀ᵒ = ℓ₀ᵒ}{ℓ₀ʰ} A = A Map.⇒₀ᵗ s {ℓᵒ = ℓ₀ᵒ}{ℓ₀ʰ}
