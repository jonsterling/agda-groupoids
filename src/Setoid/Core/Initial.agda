{-# OPTIONS --without-K #-}

module Setoid.Core.Initial where

open import Agda.Primitive
import Setoid.Core.Base as S
import Setoid.Core.Hom as Π
open import Type as T
  using (_,_)

s : ∀ {d} → S.t d lzero lzero
S.obj s = T.𝟘.t
S.homᵗ s = λ {((), _)}
S.idnᵗ s = λ {}
S.cmpᵗ s = λ {}
S.invᵗ s = λ {}

¡ : ∀ {d} ..{ℓᵒ ℓʰ}
  → {A : S.t d ℓᵒ ℓʰ}
  → s Π.⇒₀ᵗ A
Π._$₀_ ¡ = λ ()
Π._$₁_ ¡ = λ {}

¬_
  : ∀ {d} ..{ℓᵒ ℓʰ}
  → (A : S.t d ℓᵒ ℓʰ)
  → Set (ℓᵒ ⊔ ℓʰ)
¬ A = A Π.⇒₀ᵗ s
