{-# OPTIONS --without-K #-}

module Groupoid.Exponential where

open import Agda.Primitive
import Groupoid.Base as G
open import Groupoid.Exponential.Boot public
import Groupoid.Homotopy as TFor
import Setoid as S
open import Type as T
  using (_,_)

infixr 2 _⇒₀ᵍ_

_⇒₀ᵍ_ : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  → (B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
  → G.t d _ _ _
G.obj (A ⇒₀ᵍ B) =
  A ⇒₀ᵗ B
G.homˢ (A ⇒₀ᵍ B) =
  λ {(F , G) → F TFor.⇒₁ˢ G}
G.idnˢᵐ (A ⇒₀ᵍ B) =
  λ {F} → TFor.idnˢᵐ F
G.cmpˢᵐ (A ⇒₀ᵍ B) =
  TFor.cmpˢᵐ
G.invˢᵐ (_⇒₀ᵍ_ {G.Dir.≤} A B) =
  _
G.invˢᵐ (_⇒₀ᵍ_ {G.Dir.≈} A B) =
  TFor.invˢᵐ
TFor.com₂ (G.idn-lhs (A ⇒₀ᵍ B) α) =
  G.idn-lhs B (TFor.com₁ α)
TFor.com₂ (G.idn-rhs (A ⇒₀ᵍ B) α) =
  G.idn-rhs B (TFor.com₁ α)
TFor.com₂ (G.cmp-ass (A ⇒₀ᵍ B) α β γ) =
  G.cmp-ass B (TFor.com₁ α) (TFor.com₁ β) (TFor.com₁ γ)
G.inv-lhs (_⇒₀ᵍ_ {G.Dir.≤} A B) =
  _
TFor.com₂ (G.inv-lhs (_⇒₀ᵍ_ {G.Dir.≈} A B) α) =
  G.inv-lhs B (TFor.com₁ α)
G.inv-rhs (_⇒₀ᵍ_ {G.Dir.≤} A B) f =
  _
TFor.com₂ (G.inv-rhs (_⇒₀ᵍ_ {G.Dir.≈} A B) α) =
  G.inv-rhs B (TFor.com₁ α)
