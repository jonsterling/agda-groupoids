{-# OPTIONS --without-K #-}

module Ambient.Type.Discrete where

open import Agda.Primitive
import Ambient.Type.Map.Boot as Map
open import Ambient.Type.Tensor as Ten
  using (_,_)
import Ambient.Type.Terminal as 𝟙

data t ..{ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : t a a
{-# BUILTIN EQUALITY t #-}
{-# BUILTIN REFL refl #-}

-- primitive
--   primTrustMe : ∀ {ℓ} {A : Set ℓ} {a b : A} → t a b

idn
  : ∀ ..{ℓ} {A : Set ℓ} {a : A}
  → 𝟙.t⁰ Map.⇒₀ t a a
idn = Map.elm refl

cmp
  : ∀ ..{ℓ} {A : Set ℓ} {a b c : A}
  → t b c Ten.⊗ t a b Map.⇒₀ t a c
cmp (refl , refl) = refl

inv
  : ∀ ..{ℓ} {A : Set ℓ} {a b : A}
  → t a b Map.⇒₀ t b a
inv refl = refl

_$₁_
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁} {a b}
  → (F : A Map.⇒₀ B)
  → (t a b Map.⇒₀ t (F a) (F b))
_$₁_ f refl = refl

subst
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {a b}
  → (Ψ : A → Set (ℓ₀ ⊔ ℓ₁))
  → (f : t a b)
  → ((ψ : Ψ a) → Ψ b)
subst Ψ refl ψ = ψ

idn-lhs
  : ∀ ..{ℓ}
  → ∀ {A : Set ℓ} {a b : A}
  → (ϕ : t a b)
  → t (cmp (idn 𝟙.* , ϕ)) ϕ
idn-lhs refl = refl

idn-rhs
  : ∀ ..{ℓ}
  → ∀ {A : Set ℓ} {a b : A}
  → (ϕ : t a b)
  → t (cmp (ϕ , idn 𝟙.*)) ϕ
idn-rhs refl = refl

cmp-ass
  : ∀ ..{ℓ}
  → ∀ {A : Set ℓ} {a b c d : A}
  → (ϕ : t a b) (ψ : t b c) (ϑ : t c d)
  → t (cmp (cmp (ϑ , ψ) , ϕ)) (cmp (ϑ , cmp (ψ , ϕ)))
cmp-ass refl refl refl = refl

inv-lhs
  : ∀ ..{ℓ}
  → ∀ {A : Set ℓ} {a b : A}
  → (ϕ : t a b)
  → t (cmp (inv ϕ , ϕ)) refl
inv-lhs refl = refl

inv-rhs
  : ∀ ..{ℓ}
  → ∀ {A : Set ℓ} {a b : A}
  → (ϕ : t a b)
  → t refl (cmp (ϕ , inv ϕ))
inv-rhs refl = refl

J'
  : ∀ {ℓ₀ ℓ₁} {A : Set ℓ₀} {a : A}
  → (Φ : (b : A) → t a b → Set ℓ₁)
  → (ϕ : Φ a refl)
  → ((b : A) (ψ : t a b) → Φ b ψ)
J' Φ ϕ b refl = ϕ

J
  : ∀ {ℓ₀ ℓ₁} {A : Set ℓ₀}
  → (Φ : (a b : A) → t a b → Set ℓ₁)
  → (ϕ : (a : A) → Φ a a refl)
  → ((a b : A) (ψ : t a b) → Φ a b ψ)
J Φ ϕ a = J' (Φ a) (ϕ a)
