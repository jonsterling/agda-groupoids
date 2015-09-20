{-# OPTIONS --sized-types --without-K #-}

module Groupoid.Exponential where

open import Agda.Primitive
import Groupoid.Base as G
open import Groupoid.Exponential.Boot public
import Groupoid.Homotopy as Homo
import Setoid as S
open import Type as T
  using (_,_)

infixr 2 _⇒₀ᵍ_

-- FIXME: setoid morphisms
_⇒₀ᵍ_ : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  → (B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
  → G.t _ _ _
G.obj (A ⇒₀ᵍ B) =
  A ⇒₀ᵗ B
G.homˢ (A ⇒₀ᵍ B) =
  λ {(F , G) → F Homo.⇒₁ˢ G}
G.idnˢᵐ (A ⇒₀ᵍ B) = λ {F} →
  S.Π.! (Homo.idn F T.𝟙.*)
S.Π._$₀_ (G.cmpˢᵐ (A ⇒₀ᵍ B)) =
  Homo.cmp
Homo.com₂ (S.Π._$₁_ (G.cmpˢᵐ (A ⇒₀ᵍ B)) (g⇒₂ , f⇒₂)) =
  G.cmpˢᵐ B S.Π.$₁ (Homo.com₂ g⇒₂ , Homo.com₂ f⇒₂)
S.Π._$₀_ (G.invˢᵐ (A ⇒₀ᵍ B)) =
  Homo.inv
Homo.com₂ (S.Π._$₁_ (G.invˢᵐ (A ⇒₀ᵍ B)) f⇒₂) =
  G.invˢᵐ B S.Π.$₁ Homo.com₂ f⇒₂
Homo.com₂ (G.idn-lhs (A ⇒₀ᵍ B) α) =
  G.idn-lhs B (Homo.com₁ α)
Homo.com₂ (G.idn-rhs (A ⇒₀ᵍ B) α) =
  G.idn-rhs B (Homo.com₁ α)
Homo.com₂ (G.cmp-ass (A ⇒₀ᵍ B) α β γ) =
  G.cmp-ass B (Homo.com₁ α) (Homo.com₁ β) (Homo.com₁ γ)
Homo.com₂ (G.inv-lhs (A ⇒₀ᵍ B) α) =
  G.inv-lhs B (Homo.com₁ α)
Homo.com₂ (G.inv-rhs (A ⇒₀ᵍ B) α) =
  G.inv-rhs B (Homo.com₁ α)
