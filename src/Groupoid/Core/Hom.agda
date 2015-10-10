{-# OPTIONS --without-K #-}

module Groupoid.Core.Hom where

open import Agda.Primitive
import Groupoid.Core.Base as G
open import Groupoid.Core.Hom.Boot public
import Groupoid.Core.Homotopy as TF
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
  λ {(F , G) → F TF.⇒₁ˢ G}
G.idnˢᵐ (A ⇒₀ᵍ B) =
  λ {F} → TF.idnˢᵐ F
G.cmpˢᵐ (A ⇒₀ᵍ B) =
  TF.cmpˢᵐ
G.invˢᵐ (_⇒₀ᵍ_ {G.Dir.≤} A B) =
  _
G.invˢᵐ (_⇒₀ᵍ_ {G.Dir.≈} A B) =
  TF.invˢᵐ
TF.com₂ (G.idn-lhs (A ⇒₀ᵍ B) α) =
  G.idn-lhs B (TF.com₁ α)
TF.com₂ (G.idn-rhs (A ⇒₀ᵍ B) α) =
  G.idn-rhs B (TF.com₁ α)
TF.com₂ (G.cmp-ass (A ⇒₀ᵍ B) α β γ) =
  G.cmp-ass B (TF.com₁ α) (TF.com₁ β) (TF.com₁ γ)
G.inv-lhs (_⇒₀ᵍ_ {G.Dir.≤} A B) =
  _
TF.com₂ (G.inv-lhs (_⇒₀ᵍ_ {G.Dir.≈} A B) α) =
  G.inv-lhs B (TF.com₁ α)
G.inv-rhs (_⇒₀ᵍ_ {G.Dir.≤} A B) f =
  _
TF.com₂ (G.inv-rhs (_⇒₀ᵍ_ {G.Dir.≈} A B) α) =
  G.inv-rhs B (TF.com₁ α)
