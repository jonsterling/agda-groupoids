{-# OPTIONS --without-K #-}

module Setoid.Initial where

open import Agda.Primitive
import Setoid.Base as S
import Setoid.Exponential as Π
open import Type as T
  using (_,_)

s : S.t lzero lzero
S.obj s = T.𝟘.t
S.homᵗ s = λ {((), _)}
S.idnᵗᵐ s = λ {}
S.cmpᵗᵐ s = λ {}
S.invᵗᵐ s = λ {}

¡ : ∀ ..{ℓᵒ ℓʰ} {A : S.t ℓᵒ ℓʰ} → s Π.⇒₀ᵗ A
Π._$₀_ ¡ = λ ()
Π._$₁_ ¡ = λ {}

¬_ : ∀ ..{ℓᵒ ℓʰ} (A : S.t ℓᵒ ℓʰ) → Set (ℓᵒ ⊔ ℓʰ)
¬ A = A Π.⇒₀ᵗ s
