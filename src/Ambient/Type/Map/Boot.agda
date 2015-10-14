{-# OPTIONS --without-K #-}

module Ambient.Type.Map.Boot where

open import Agda.Primitive
open import Ambient.Type.Tensor.Boot as Ten
  using (_,_)

infixr 0 _⇒₀_
infixr 1 _∘_

_⇒₀_
  : ∀ ..{ℓ₀ ℓ₁}
  → (A : Set ℓ₀) (B : Set ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
A ⇒₀ B = A → B

idn
  : ∀ {ℓ} {A : Set ℓ}
  → A ⇒₀ A
idn x = x

cmp
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → (GF : (B ⇒₀ C) Ten.⊗ (A ⇒₀ B))
  → (A ⇒₀ C)
cmp (g , f) x = g (f x)

elm : ∀ ..{ℓ₀ ℓ₁}
  → {A : Set ℓ₀} {B : Set ℓ₁}
  → A → (B ⇒₀ A)
elm x _ = x

_∘_
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → (g : B ⇒₀ C)
  → (f : A ⇒₀ B)
  → (A ⇒₀ C)
g ∘ f = cmp (g , f)
