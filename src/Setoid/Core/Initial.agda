{-# OPTIONS --without-K #-}

module Setoid.Core.Initial where

open import Agda.Primitive
import Setoid.Core.Base as S
import Setoid.Core.Hom as Π
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
  → s {ℓᵒ = ℓ₀ᵒ}{ℓ₀ʰ} Π.⇒₀ᵗ A
Π._$₀_ ¡ = λ ()
Π._$₁_ ¡ = λ {}

¬_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t d ℓ₁ᵒ ℓ₁ʰ)
  → Set _
¬_ {ℓ₀ᵒ = ℓ₀ᵒ}{ℓ₀ʰ} A = A Π.⇒₀ᵗ s {ℓᵒ = ℓ₀ᵒ}{ℓ₀ʰ}
