{-# OPTIONS --without-K #-}

open import Common
module Groupoid.Profunctor {d : Dir.t} where

open import Agda.Primitive
private
  module G where
    open import Groupoid public
      hiding (module Π; module TF)
    module Π where
      open Groupoid.Π public
      open import Groupoid.Bifunctor public
import Setoid as S
open import Type as T
  using (_,_)

module _ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ} where
  infixr 0 _:[_]⇏₀ᵗ_

  _:[_]⇏₀ᵗ_
    : (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (V : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → (B : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ)
    → Set _
  A :[ V ]⇏₀ᵗ B = G.Π.:⟨ G.Op.g B , A ⟩⇒₀ᵗ V

  _:[_]⇏₀ᵍ_
    : (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (V : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → (B : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ)
    → G.t _ _ _ _
  A :[ V ]⇏₀ᵍ B = G.Π.:⟨ G.Op.g B , A ⟩⇒₀ᵍ V

!:[_]₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → (V : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
  → (d : G.obj V)
  → A :[ V ]⇏₀ᵗ A
!:[ V ]₀ d = G.Π.!ᵍ d
