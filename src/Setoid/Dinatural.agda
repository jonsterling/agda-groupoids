{-# OPTIONS --without-K #-}

module Setoid.Dinatural where

open import Agda.Primitive
import Setoid as S
open import Type as T
  using (_,_)

infixr 0 _:⇏₁_

record _:⇏₁_
  {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  (F G : S.Op.s A S.∐.⊗ A S.Π.⇒₀ᵗ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ʰ) where
  no-eta-equality
  field
    com₁
      : ∀ {a}
      → S.homᵗ B (F S.Π.$₀ (a , a) , G S.Π.$₀ (a , a))
open _:⇏₁_ public
