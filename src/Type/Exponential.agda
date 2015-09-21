{-# OPTIONS --without-K #-}

module Type.Exponential where

open import Agda.Primitive
open import Type.Exponential.Boot public
open import Type.Tensor.Boot as ∐
  using (_,_)

infixr 1 _∘_

_∘_
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : A → Set ℓ₁} {C : ∀ {a} → B a → Set ℓ₂}
  → (g : ∀ {a} → t (B a) C)
  → (f : t A B)
  → (t A (λ a → C (f a)))
g ∘ f = cmp (g , f)

! : ∀ ..{ℓ₀ ℓ₁}
  → {A : Set ℓ₀} {B : Set ℓ₁}
  → A → (B ⇒₀ A)
! x _ = x
