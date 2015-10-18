{-# OPTIONS --without-K #-}

module Ambient.Setoid.Tensor.Boot where

open import Agda.Primitive
import Ambient.Setoid.Base as S
open import Type as T

infixr 3 _⊗_

_⊗_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ)
  → (B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ)
  → S.𝔊₁ d _ _
S.cell₀ (A ⊗ B) =
  S.𝔊₁.cell₀ A ×₀ S.𝔊₁.cell₀ B
S.cell₁ (A ⊗ B) =
  λ {((a₀ , b₀) , (a₁ , b₁)) →
    S.cell₁ A (a₀ , a₁) ×₀ S.cell₁ B (b₀ , b₁)
  }
S.idn (A ⊗ B) =
  ⟨ S.idn A ,₀ S.idn B ⟩
S.cmp (A ⊗ B) =
  ⟨  S.cmp A ⇒₀.∘₀ ⟨ π⁰₀ ×₀ π⁰₀ ⟩
  ,₀ S.cmp B ⇒₀.∘₀ ⟨ π¹₀ ×₀ π¹₀ ⟩ ⟩
S.inv (_⊗_ {S.Dir.≤} A B) =
  _
S.inv (_⊗_ {S.Dir.≈} A B) =
  ⟨ S.inv A ×₀ S.inv B ⟩
