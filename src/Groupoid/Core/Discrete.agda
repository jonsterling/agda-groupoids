{-# OPTIONS --without-K #-}

module Groupoid.Core.Discrete where

open import Agda.Primitive
import Groupoid.Core.Base as G
import Setoid as S
open import Type as T
  using (_,_)

-- FIXME: separate out the setoid morphisms

g : ∀ {d} ..{ℓᵒ}
  → (A : T.t ℓᵒ)
  → G.t d _ _ _
G.obj (g A) =
  A
G.homˢ (g A) =
  λ {(a , b) → S.≡.s (a T.≡.t b)}
S.Π._$₀_ (G.idnˢ (g A)) =
  T.≡.idn
S.Π._$₁_ (G.idnˢ (g A)) =
  T.≡.idn
S.Π._$₀_ (G.cmpˢ (g A)) =
  T.≡.cmp
S.Π._$₁_ (G.cmpˢ (g {ℓᵒ = ℓᵒ} A)) = λ { {(_ , _)} (g , f) →
    T.≡.subst {ℓ₁ = ℓᵒ} (λ _ → _ T.≡.t _) g
   (T.≡.subst {ℓ₁ = ℓᵒ} (λ _ → _ T.≡.t _) f
    T.≡.refl)
  }
G.invˢ (g {G.Dir.≤} A) =
  _
S.Π._$₀_ (G.invˢ (g {G.Dir.≈} A)) =
  T.≡.inv
S.Π._$₁_ (G.invˢ (g {G.Dir.≈} {ℓᵒ = ℓᵒ} A)) = λ α →
    T.≡.subst {ℓ₁ = ℓᵒ} (λ _ → _ T.≡.t _) α
    T.≡.refl
G.idn-lhs (g A) =
  T.≡.idn-lhs
G.idn-rhs (g A) =
  T.≡.idn-rhs
G.cmp-ass (g A) =
  T.≡.cmp-ass
G.inv-lhs (g {G.Dir.≤} A) =
  _
G.inv-lhs (g {G.Dir.≈} A) =
  T.≡.inv-lhs
G.inv-rhs (g {G.Dir.≤} A) =
  _
G.inv-rhs (g {G.Dir.≈} A) =
  T.≡.inv-rhs
