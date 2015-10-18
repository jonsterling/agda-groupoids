{-# OPTIONS --without-K #-}

module Ambient.Type.Map.Boot where

open import Agda.Primitive
open import Ambient.Type.Product.Boot

infixr 0 _⇒₀,₀_
infixl 0 _·₀,₀_
infixr 1 _∘₀_

_⇒₀,₀_
  : ∀ ..{ℓ₀ ℓ₁}
  → (A : Set ℓ₀) (B : Set ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
A ⇒₀,₀ B = A → B

_·₀,₀_
  : ∀ ..{ℓ₀ ℓ₁}
  → {A : Set ℓ₀} {B : Set ℓ₁}
  → A ⇒₀,₀ B
  → ((x : A) → B)
f ·₀,₀ x = f x

idn₀
  : ∀ {ℓ} {A : Set ℓ}
  → A ⇒₀,₀ A
idn₀ x = x

cmp₀
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → (GF : (B ⇒₀,₀ C) ×₀ (A ⇒₀,₀ B))
  → (A ⇒₀,₀ C)
cmp₀ (g , f) x = g (f x)

elm₀ : ∀ ..{ℓ₀ ℓ₁}
  → {A : Set ℓ₀} {B : Set ℓ₁}
  → A → (B ⇒₀,₀ A)
elm₀ x _ = x

_∘₀_
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → (g : B ⇒₀,₀ C)
  → (f : A ⇒₀,₀ B)
  → (A ⇒₀,₀ C)
g ∘₀ f = cmp₀ (g , f)
