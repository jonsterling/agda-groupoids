{-# OPTIONS --without-K #-}

module Ambient.Groupoid.Discrete where

open import Agda.Primitive
import Ambient.Groupoid.Base as G
import Setoid as S
open import Type as T

-- FIXME: separate out the setoid morphisms

g : ∀ {d} ..{ℓᵒ}
  → (A : T.𝔊₀ ℓᵒ)
  → G.𝔊₂,₀ d _ _ _
G.obj (g A) =
  A
G.homˢ (g A) =
  λ {(a , b) → S.≡.s (a T.≡₀ b)}
S.Map._$₀_ (G.idnˢ (g A)) =
  ≡₀.idn
S.Map._$₁_ (G.idnˢ (g A)) =
  ≡₀.idn
S.Map._$₀_ (G.cmpˢ (g A)) =
  ≡₀.cmp
S.Map._$₁_ (G.cmpˢ (g {ℓᵒ = ℓᵒ} A)) = λ { {(_ , _)} (g , f) →
    ≡₀.subst {ℓ₁ = ℓᵒ} (λ _ → _ T.≡₀ _) g
   (≡₀.subst {ℓ₁ = ℓᵒ} (λ _ → _ T.≡₀ _) f
    ≡₀.refl)
  }
G.invˢ (g {G.Dir.≤} A) =
  _
S.Map._$₀_ (G.invˢ (g {G.Dir.≈} A)) =
  ≡₀.inv
S.Map._$₁_ (G.invˢ (g {G.Dir.≈} {ℓᵒ = ℓᵒ} A)) = λ α →
    ≡₀.subst {ℓ₁ = ℓᵒ} (λ _ → _ T.≡₀ _) α
    ≡₀.refl
G.idn-lhs (g A) =
  ≡₀.idn-lhs
G.idn-rhs (g A) =
  ≡₀.idn-rhs
G.cmp-ass (g A) =
  ≡₀.cmp-ass
G.inv-lhs (g {G.Dir.≤} A) =
  _
G.inv-lhs (g {G.Dir.≈} A) =
  ≡₀.inv-lhs
G.inv-rhs (g {G.Dir.≤} A) =
  _
G.inv-rhs (g {G.Dir.≈} A) =
  ≡₀.inv-rhs
