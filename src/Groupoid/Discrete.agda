{-# OPTIONS --without-K #-}

module Groupoid.Discrete where

open import Agda.Primitive
import Groupoid.Base as G
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
  λ {(a , b) → S.Discrete.s (T.Discrete.t a b)}
S.Π._$₀_ (G.idnˢᵐ (g A)) =
  T.Discrete.idn
S.Π._$₁_ (G.idnˢᵐ (g A)) =
  T.Discrete.idn
S.Π._$₀_ (G.cmpˢᵐ (g A)) =
  T.Discrete.cmp
S.Π._$₁_ (G.cmpˢᵐ (g {ℓᵒ = ℓᵒ} A)) = λ { {(_ , _)} (g , f) →
    T.Discrete.subst {ℓ₁ = ℓᵒ} (λ _ → T.Discrete.t _ _) g
   (T.Discrete.subst {ℓ₁ = ℓᵒ} (λ _ → T.Discrete.t _ _) f
    T.Discrete.refl)
  }
G.invˢᵐ (g {G.Dir.≤} A) =
  _
S.Π._$₀_ (G.invˢᵐ (g {G.Dir.≈} A)) =
  T.Discrete.inv
S.Π._$₁_ (G.invˢᵐ (g {G.Dir.≈} {ℓᵒ = ℓᵒ} A)) = λ α →
    T.Discrete.subst {ℓ₁ = ℓᵒ} (λ _ → T.Discrete.t _ _) α
    T.Discrete.refl
G.idn-lhs (g A) =
  T.Discrete.idn-lhs
G.idn-rhs (g A) =
  T.Discrete.idn-rhs
G.cmp-ass (g A) =
  T.Discrete.cmp-ass
G.inv-lhs (g {G.Dir.≤} A) =
  _
G.inv-lhs (g {G.Dir.≈} A) =
  T.Discrete.inv-lhs
G.inv-rhs (g {G.Dir.≤} A) =
  _
G.inv-rhs (g {G.Dir.≈} A) =
  T.Discrete.inv-rhs
