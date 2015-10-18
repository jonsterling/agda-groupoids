{-# OPTIONS --without-K #-}

module Ambient.Type.Initial where

open import Agda.Primitive

data 𝟘₀ ..{ℓ} : Set ℓ where

¡₀ : ∀ ..{ℓ} {A : Set ℓ} → 𝟘₀ {lzero} → A
¡₀ ()

¬₀_ : ∀ ..{ℓ} → Set ℓ → Set ℓ
¬₀_ A = A → 𝟘₀ {lzero}
