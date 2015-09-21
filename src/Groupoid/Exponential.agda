{-# OPTIONS --without-K #-}

module Groupoid.Exponential where

open import Agda.Primitive
import Groupoid.Base as G
open import Groupoid.Exponential.Boot public
import Setoid as S
import Groupoid.Transfor as TFor
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
  λ {(F , G) → F TFor.⇒₁ˢ G}
G.idnˢᵐ (A ⇒₀ᵍ B) = λ {F} →
  S.Π.! (TFor.idn F T.𝟙.*)
S.Π._$₀_ (G.cmpˢᵐ (A ⇒₀ᵍ B)) =
  TFor.cmp
TFor.com₂ (S.Π._$₁_ (G.cmpˢᵐ (A ⇒₀ᵍ B)) (g⇒₂ , f⇒₂)) =
  G.cmpˢᵐ B S.Π.$₁ (TFor.com₂ g⇒₂ , TFor.com₂ f⇒₂)
S.Π._$₀_ (G.invˢᵐ (A ⇒₀ᵍ B)) =
  TFor.inv
TFor.com₂ (S.Π._$₁_ (G.invˢᵐ (A ⇒₀ᵍ B)) f⇒₂) =
  G.invˢᵐ B S.Π.$₁ TFor.com₂ f⇒₂
TFor.com₂ (G.idn-lhs (A ⇒₀ᵍ B) α) =
  G.idn-lhs B (TFor.com₁ α)
TFor.com₂ (G.idn-rhs (A ⇒₀ᵍ B) α) =
  G.idn-rhs B (TFor.com₁ α)
TFor.com₂ (G.cmp-ass (A ⇒₀ᵍ B) α β γ) =
  G.cmp-ass B (TFor.com₁ α) (TFor.com₁ β) (TFor.com₁ γ)
TFor.com₂ (G.inv-lhs (A ⇒₀ᵍ B) α) =
  G.inv-lhs B (TFor.com₁ α)
TFor.com₂ (G.inv-rhs (A ⇒₀ᵍ B) α) =
  G.inv-rhs B (TFor.com₁ α)
