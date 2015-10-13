{-# OPTIONS --without-K #-}

open import Common
module Groupoid.Wedge {d : Dir.t} where

open import Agda.Primitive
private
  module G where
    open import Groupoid public
      hiding (module Π; module TF)
    module Π where
      open Groupoid.Π public
      open import Groupoid.Bifunctor public
      open import Groupoid.Profunctor public
    module TF where
      open Groupoid.TF public
      open import Groupoid.Dinatural public
import Setoid as S
open import Type as T
  using (_,_)

Δ:[_]₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → (V : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
  → (P : A G.Π.:[ V ]⇏₀ᵗ A)
  → (d : G.obj V)
  → Set _
Δ:[ V ]₀ P d = G.Π.!:[ V ]₀ d G.TF.:⇏₁ᵗ P

∇:[_]₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → (V : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
  → (P : A G.Π.:[ V ]⇏₀ᵗ A)
  → (d : G.obj V)
  → Set _
∇:[ V ]₀ P d = P G.TF.:⇏₁ᵗ G.Π.!:[ V ]₀ d
