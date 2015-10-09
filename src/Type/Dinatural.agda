{-# OPTIONS --without-K #-}

module Type.Dinatural where

open import Agda.Primitive
open import Type as T
  using (_,_)

infixr 0 _:⇏₁_

record _:⇏₁_ ..{ℓ₀ᵒ ℓ₁ᵒ}
  {A : T.t ℓ₀ᵒ}
  {B : T.t ℓ₁ᵒ}
  (F G : (T.Op.t A T.∐.⊗ A) T.Π.⇒₀ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ᵒ) where
  no-eta-equality
  field
    com₁
      : ∀ {x}
      → F (x , x) T.≡.t G (x , x)
open _:⇏₁_ public
