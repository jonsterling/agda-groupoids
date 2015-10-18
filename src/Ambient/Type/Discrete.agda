{-# OPTIONS --without-K #-}

module Ambient.Type.Discrete where

open import Agda.Primitive
open import Ambient.Type.Map.Boot
open import Ambient.Type.Product
open import Ambient.Type.Terminal

data _≡₀_ ..{ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : a ≡₀ a
{-# BUILTIN EQUALITY _≡₀_ #-}
{-# BUILTIN REFL refl #-}

-- primitive
--   primTrustMe : ∀ {ℓ} {A : Set ℓ} {a b : A} → t a b

idn
  : ∀ ..{ℓ} {A : Set ℓ} {a : A}
  → 𝟙₀ {lzero} ⇒₀,₀ a ≡₀ a
idn = elm₀ refl

cmp
  : ∀ ..{ℓ} {A : Set ℓ} {a b c : A}
  → (b ≡₀ c) ×₀ (a ≡₀ b) ⇒₀,₀ (a ≡₀ c)
cmp (refl , refl) = refl

inv
  : ∀ ..{ℓ} {A : Set ℓ} {a b : A}
  → a ≡₀ b ⇒₀,₀ b ≡₀ a
inv refl = refl

_$₁_
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁} {a b}
  → (F : A ⇒₀,₀ B)
  → (a ≡₀ b) ⇒₀,₀ (F a ≡₀ F b)
_$₁_ f refl = refl

subst
  : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {a b}
  → (Ψ : A → Set (ℓ₀ ⊔ ℓ₁))
  → (f : a ≡₀ b)
  → ((ψ : Ψ a) → Ψ b)
subst Ψ refl ψ = ψ

idn-lhs
  : ∀ ..{ℓ}
  → ∀ {A : Set ℓ} {a b : A}
  → (ϕ : a ≡₀ b)
  → cmp (idn * , ϕ) ≡₀ ϕ
idn-lhs refl = refl

idn-rhs
  : ∀ ..{ℓ}
  → ∀ {A : Set ℓ} {a b : A}
  → (ϕ : a ≡₀ b)
  → cmp (ϕ , idn *) ≡₀ ϕ
idn-rhs refl = refl

cmp-ass
  : ∀ ..{ℓ}
  → ∀ {A : Set ℓ} {a b c d : A}
  → (ϕ : a ≡₀ b) (ψ : b ≡₀ c) (ϑ : c ≡₀ d)
  → cmp (cmp (ϑ , ψ) , ϕ) ≡₀ cmp (ϑ , cmp (ψ , ϕ))
cmp-ass refl refl refl = refl

inv-lhs
  : ∀ ..{ℓ}
  → ∀ {A : Set ℓ} {a b : A}
  → (ϕ : a ≡₀ b)
  → cmp (inv ϕ , ϕ) ≡₀ refl
inv-lhs refl = refl

inv-rhs
  : ∀ ..{ℓ}
  → ∀ {A : Set ℓ} {a b : A}
  → (ϕ : a ≡₀ b)
  → refl ≡₀ cmp (ϕ , inv ϕ)
inv-rhs refl = refl

J'
  : ∀ {ℓ₀ ℓ₁} {A : Set ℓ₀} {a : A}
  → (Φ : (b : A) → a ≡₀ b → Set ℓ₁)
  → (ϕ : Φ a refl)
  → ((b : A) (ψ : a ≡₀ b) → Φ b ψ)
J' Φ ϕ b refl = ϕ

J
  : ∀ {ℓ₀ ℓ₁} {A : Set ℓ₀}
  → (Φ : (a b : A) → a ≡₀ b → Set ℓ₁)
  → (ϕ : (a : A) → Φ a a refl)
  → ((a b : A) (ψ : a ≡₀ b) → Φ a b ψ)
J Φ ϕ a = J' (Φ a) (ϕ a)
