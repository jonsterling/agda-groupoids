{-# OPTIONS --without-K #-}

module Type.Core.Hom where

open import Agda.Primitive
open import Type.Core.Hom.Boot public
open import Type.Core.Tensor.Boot as ∐
  using (_,_)

infixr 1 _∘_

_∘_
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → (g : B ⇒₀ C)
  → (f : A ⇒₀ B)
  → (A ⇒₀ C)
g ∘ f = cmp (g , f)

! : ∀ ..{ℓ₀ ℓ₁}
  → {A : Set ℓ₀} {B : Set ℓ₁}
  → A → (B ⇒₀ A)
! x _ = x
