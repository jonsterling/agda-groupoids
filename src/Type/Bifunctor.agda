{-# OPTIONS --without-K #-}

module Type.Bifunctor where

open import Agda.Primitive
open import Type as T
  using (_,_)

infixr 0 :[_,_]⇒₀_

:[_,_]⇒₀_
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → (A : T.t ℓ₀ᵒ) (B : T.t ℓ₁ᵒ) (C : T.t ℓ₂ᵒ)
  → Set _
:[ A , B ]⇒₀ C = A T.∐.⊗ B T.Π.⇒₀ C
