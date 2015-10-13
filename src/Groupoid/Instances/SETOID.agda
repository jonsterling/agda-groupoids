{-# OPTIONS --without-K #-}

module Groupoid.Instances.SETOID where

open import Agda.Primitive
private
  module G where
    open import Groupoid public
    module ≅ where
      open import Groupoid.Iso public
import Setoid as S
open import Type as T
  using (_,_)

c : ..(ℓᵒ ℓʰ : _) → G.t S.Dir.≤ _ _ _
G.obj (c ℓᵒ ℓʰ) =
  S.t S.Dir.≈ ℓᵒ ℓʰ
G.homˢ (c _ _) =
  λ {(a , b) → a S.Π.⇒₀ˢ b}
G.idnˢ (c _ _) =
  S.Π.idn₀ˢ
G.cmpˢ (c _ _) =
  S.Π.cmp₀ˢ
S.TF.com₁ (G.idn-lhs (c _ _) {b = B} _) =
  S.idnᵗ B _
S.TF.com₁ (G.idn-rhs (c _ _) {b = B} _) =
  S.idnᵗ B _
S.TF.com₁ (G.cmp-ass (c _ _) {d = D} _ _ _) =
  S.idnᵗ D _
G.invˢ (c _ _) =
  _
G.inv-lhs (c _ _) =
  _
G.inv-rhs (c _ _) =
  _

g : ∀ d ..(ℓᵒ ℓʰ : _) → G.t d _ _ _
g d ℓᵒ ℓʰ = G.≅.g d (c ℓᵒ ℓʰ)
