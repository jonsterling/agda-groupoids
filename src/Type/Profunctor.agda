{-# OPTIONS --without-K #-}

module Type.Profunctor where

open import Agda.Primitive
import Type.Bifunctor 
open import Type as T
  using (_,_)

infixr 0 _:[_]⇏₀_

_:[_]⇏₀_
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → (A : T.t ℓ₀ᵒ) (V : T.t ℓ₁ᵒ) (B : T.t ℓ₂ᵒ)
  → Set _
_:[_]⇏₀_ = 
-- A T.∐.⊗ B T.Π.⇒₀ C
