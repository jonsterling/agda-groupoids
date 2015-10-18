{-# OPTIONS --without-K #-}

open import Common
module Groupoid.Presheaf {d : Dir.t} where

open import Agda.Primitive
import Groupoid as G
import Setoid as S
open import Type as T
  using (_,_)

module _ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} where
  infixr 0 _⇏₀ᵗ_
  infixr 2 _⇏₀ᵍ_

  _⇏₀ᵗ_
    : (A : G.𝔊₂,₀ d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (V : G.𝔊₂,₀ d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → Set _
  A ⇏₀ᵗ V = G.Op.g A G.Map.⇒₀ᵗ V

  _⇏₀ᵍ_
    : (A : G.𝔊₂,₀ d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (V : G.𝔊₂,₀ d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → G.𝔊₂,₀ _ _ _ _
  A ⇏₀ᵍ V = G.Op.g A G.Map.⇒₀ᵍ V
