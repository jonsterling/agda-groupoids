{-# OPTIONS --without-K #-}

open import Common
module Groupoid.Profunctor {d : Dir.t} where

open import Agda.Primitive
private
  module G where
    open import Groupoid public
      hiding (module Map)
    module Map where
      open Groupoid.Map public
      open import Groupoid.Bifunctor public
import Setoid as S
open import Type as T
  using (_,_)

module _ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ} where
  infixr 0 _:[_]⇏₀ᵗ_

  _:[_]⇏₀ᵗ_
    : (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (𝒱 : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → (B : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ)
    → Set _
  A :[ 𝒱 ]⇏₀ᵗ B = G.Map.:⟨ G.Op.g B , A ⟩⇒₀ᵗ 𝒱

  _:[_]⇏₀ᵍ_
    : (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (𝒱 : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → (B : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ)
    → G.t _ _ _ _
  A :[ 𝒱 ]⇏₀ᵍ B = G.Map.:⟨ G.Op.g B , A ⟩⇒₀ᵍ 𝒱

!:[_]₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → (𝒱 : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
  → (d : G.obj 𝒱)
  → A :[ 𝒱 ]⇏₀ᵗ A
!:[ 𝒱 ]₀ d = G.Map.!ᵍ d
