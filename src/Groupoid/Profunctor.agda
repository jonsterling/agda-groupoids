{-# OPTIONS --without-K #-}

module Groupoid.Profunctor where

open import Agda.Primitive
module G where
  open import Groupoid public
    hiding (module Π)
  module Π where
    open Groupoid.Π public
    open import Groupoid.Bifunctor public
import Setoid as S
open import Type as T
  using (_,_)

module _ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ} where
  infixr 0 _:[_]⇏₀_

  _:[_]⇏₀_
    : (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (V : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → (B : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ)
    → Set _
  A :[ V ]⇏₀ B = G.Π.:[ G.Op.g B , A ]⇒₀ V