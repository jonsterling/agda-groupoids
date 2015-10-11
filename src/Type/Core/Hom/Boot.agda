{-# OPTIONS --without-K #-}

module Type.Core.Hom.Boot where

open import Agda.Primitive
open import Type.Core.Tensor.Boot as ∐
  using (_,_)

infixr 0 _⇒₀_

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
  → (GF : (B ⇒₀ C) ∐.⊗ (A ⇒₀ B))
  → (A ⇒₀ C)
cmp (g , f) x = g (f x)
