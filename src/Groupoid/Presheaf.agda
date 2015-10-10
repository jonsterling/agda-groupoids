{-# OPTIONS --without-K #-}

module Groupoid.Presheaf where

open import Agda.Primitive
import Groupoid as G
import Setoid as S
open import Type as T
  using (_,_)

module _ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} where
  infixr 0 _⇏₀_

  _⇏₀_
    : (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (V : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → Set _
  A ⇏₀ V = G.Op.g A G.Π.⇒₀ᵗ V
