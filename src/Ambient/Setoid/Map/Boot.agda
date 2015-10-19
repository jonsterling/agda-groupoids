{-# OPTIONS --without-K #-}

module Ambient.Setoid.Map.Boot where

open import Agda.Primitive
import Ambient.Setoid.Base as S
open import Type as T

infixr 1 _⇒₀ᵗ_
infixr 2 _∘₀ᵗ_

record _⇒₀ᵗ_
  {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  (A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ)
  (B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ʰ) ⊔ (ℓ₁ᵒ ⊔ ℓ₁ʰ)) where
  no-eta-equality
  infixr 4 _$₀_
  infixr 4 _$₁_
  field
    _$₀_
      : S.cell₀ A ⇒₀,₀ S.cell₀ B
    ._$₁_
      : ∀ {a b}
      → S.cell₁ A (a , b) ⇒₀,₀ S.cell₁ B (_$₀_ a , _$₀_ b)
open _⇒₀ᵗ_ public

idn₀ᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
  → 𝟙₀ {lzero} ⇒₀,₀ (A ⇒₀ᵗ A)
_$₀_ (idn₀ᵗ *) = ⇒₀.idn₀
_$₁_ (idn₀ᵗ *) = ⇒₀.idn₀

cmp₀ᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.𝔊₁ d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ᵗ C) ×₀ (A ⇒₀ᵗ B) ⇒₀,₀ (A ⇒₀ᵗ C)
_$₀_ (cmp₀ᵗ (G , F)) = (G $₀_) ⇒₀.∘₀ (F $₀_)
_$₁_ (cmp₀ᵗ (G , F)) = (G $₁_) ⇒₀.∘₀ (F $₁_)

_∘₀ᵗ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.𝔊₁ d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ᵗ C) ⇒₀,₀ (A ⇒₀ᵗ B) ⇒₀,₀ (A ⇒₀ᵗ C)
_∘₀ᵗ_ G F = cmp₀ᵗ (G , F)
